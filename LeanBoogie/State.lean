import LeanBoogie.Effect.Mem
import LeanBoogie.Notation.Iter
import LeanBoogie.ITree.Effect
import LeanBoogie.ConTy

namespace LeanBoogie
open ITree

/-
  The file `Mem.lean` only defines the `Mem` effect, but lacks any interpretation.
  We give one interpretation here, using `Con` and `ConA` from `LeanBoogie.ConTy`.

  You can imagine giving a completely different model for memory events in a world without
  strong consistency guarantees. I have no idea how that would look like, but it would
  be very interesting to try.
-/


/-
  # The state monad
-/


def State.read [Monad M] (v : Var Γ A) : StateT Γ M A := fun γ => return (γ.get v, γ)
def State.write [Monad M] (v : Var Γ A) (val : A) : StateT Γ M PUnit := fun γ => return (.unit, γ.set v val)

-- def State.iter [Monad M] [Iter M] {Γ A : Type} (f : A -> Γ -> M ((A ⊕ B) × Γ)) (a₀ : A) : Γ -> M (B × Γ) :=
def State.iter [Monad M] [Iter M] /- {Γ : Con} -/ (f : A -> StateT Γ M (A ⊕ B)) (a₀ : A) : StateT Γ M B :=
  fun γ => Iter.iter (fun (⟨a, γ⟩ : A × Γ) => do
    let ⟨ab, γ'⟩ <- f a γ
    match ab with
    | .inl (a : A) => return .inl ⟨a, γ'⟩ -- continue
    | .inr (b : B) => return .inr ⟨b, γ'⟩ -- done
  ) (a₀, γ)

instance [Monad M] [Iter M] : Iter (StateT Γ M) := ⟨State.iter⟩



section
/-
  # Interpreting
-/

variable {M : Type _ -> Type _} [Monad M]
variable [Iter M]

/-- We can interpret memory events into any monad, with our state monad on top. This is actually
  a family of handlers, one for every monad `M`. Although `M` is usually another `ITree _`. -/
def State.handler [Monad M] : Handler (Mem Γ) (StateT Γ M)
| _, .rd v => State.read v
| _, .wr v val => State.write v val

theorem State.interp_read {v : Var Γ A} : interp State.handler (Mem.read v) = State.read (M := M) v := by
  rw [Mem.read, interp_trigger]; rfl

theorem State.interp_write {v : Var Γ A} : interp State.handler (Mem.write v val) = (State.write (M := M) v val) := by
  rw [Mem.write, interp_trigger]; rfl
end

/-- Given an ITree which may refer to default-initialized local vars `L`, parameters `P`,
  obtain a `P -> ITree (Mem G) R`. -/
def runProc {P L : Con} {R : Type} (t : ITree (Mem (L ++ P)) R) (p : P) : ITree (Mem []) R :=
  let tL : StateT (L ++ P) (ITree (Mem [])) R := interp State.handler t
  Prod.fst <$> (tL ((default : L) ++ p))

#synth MonadLiftT (ITree (Mem ?Γ)) (StateT (ConA [?A]) (ITree (Mem ?Γ)) )

def runRes {A : Ty} (t : ITree (Mem ([A] ++ Γ)) Unit) (a : A) : ITree (Mem Γ) A :=
  let hleft  : Handler (Mem [A]        ) (StateT [A] (ITree (Mem Γ))) := State.handler
  let hright : Handler (          Mem Γ) (StateT [A] (ITree (Mem Γ))) := fun _ e => liftM (trigger e) -- this liftM feels dirty, maybe there's a better way
  let h      : Handler (Mem [A] & Mem Γ) (StateT [A] (ITree (Mem Γ))) := Handler.case hleft hright
  let t :             ITree (Mem [A] & Mem Γ)  Unit             := embed t
  let t : ConA [A] -> ITree (          Mem Γ) (Unit × ConA [A]) := interp h t
  (Prod.fst ∘ Prod.snd) <$> t (a, ())

/-
  ## Equational reasoning for our state monad

  `interp_*` lemmas show that `interp` is a monad morphism.
  We should also show properties about the interpreted state, which we can not show on the `Mem` events.
  For example, last write wins, etc.

  * A lot of theorems about how our state behaves are proven in `Types.lean`, usually named `ConA_*`.
-/

theorem State.ite_push_state [Decidable c] {t e : StateT Γ M A}
  : (if c then t else e) σ = (if c then t σ else e σ)
  := by split <;> simp_all only

theorem State.bind_push_state [Monad M] {a : StateT Γ M A} {b : A -> StateT Γ M B}
  : (a >>= b) σ = (a σ >>= fun res => b res.fst res.snd)
  := rfl
