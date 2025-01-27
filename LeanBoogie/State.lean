import LeanBoogie.Effect.Mem
import ITree
import LeanBoogie.ConTy
import LeanBoogie.ConTyNorm

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
  # The State monad
  We get almost everything for free via Lean's built-in `StateT`.
-/
variable {M : Type _ -> Type _} [Monad M] [Iter M]
variable {E F : Type -> Type}

def State.read (Γ) (v : Var Γ A) : StateT Γ M A := fun γ => return (γ.get v, γ)
def State.readAll (Γ) : StateT Γ M Γ := fun γ => return (γ, γ)
def State.write (Γ) (v : Var Γ A) (val : A) : StateT Γ M Unit := fun γ => return (.unit, γ.set v val)

def State.iter [Monad M] [Iter M] {Γ : Type} (f : A -> StateT Γ M (A ⊕ B)) (a₀ : A) : StateT Γ M B :=
  fun γ => Iter.iter (fun (⟨a, γ⟩ : A × Γ) => do
    let ⟨ab, γ'⟩ <- f a γ
    match ab with
    | .inl (a : A) => return .inl ⟨a, γ'⟩ -- continue
    | .inr (b : B) => return .inr ⟨b, γ'⟩ -- done
  ) (a₀, γ)

instance {Γ : Type} [Monad M] [Iter M] : Iter (StateT Γ M) := ⟨State.iter⟩

/-
  ## Interpreting `Mem` events into `State`
-/

/-- We can interpret memory events into any monad, with our state monad on top. This is actually
  a family of handlers, one for every monad `M`. Although `M` is usually another `ITree _`. -/
def State.handler : Handler (Mem Γ) (StateT Γ M)
| _, .rd v => State.read _ v
| _, .wr v val => State.write _ v val


abbrev State.run {R : Type} : ITree (E & Mem Γ) R -> StateT Γ (ITree E) R :=
  interp (Handler.right State.handler)

theorem State.run_right {b : A -> ITree (E & Mem Γ) B}
  : State.run (trigger (.right m) >>= b) = State.handler m >>= fun a => State.run (b a)
  := by rw [State.run, interp_bind, interp_trigger]; rfl

theorem State.run_left {b : A -> ITree (E & Mem Γ) B}
  : State.run (trigger (.left e) >>= b) = Handler.trivial e >>= fun a => State.run (b a)
  := by rw [State.run, interp_bind, interp_trigger]; rfl

/-
  ## Equational reasoning for our state monad

  `interp_*` lemmas show that `interp` is a monad morphism.
  We should also show properties about the interpreted state, which we can not show on the `Mem` events.
  For example, last write wins, etc.

  * A lot of theorems about how our state behaves are proven in `ConTy.lean`, usually named `ConA_*`.
-/

omit [Monad M] [Iter M]

@[aesop 10%] theorem State.ite_push_state [Decidable c] {t e : StateT Γ M A}
  : (if c then t else e) σ = (if c then t σ else e σ)
  := by split <;> simp_all only

@[aesop 10%] theorem State.bind_push_state [Monad M] {a : StateT Γ M A} {b : A -> StateT Γ M B}
  : (a >>= b) σ = (a σ >>= fun res => b res.fst res.snd)
  := rfl


abbrev State.handler2 (Δ Γ) (h : Handler E M) : Handler (E & Mem Δ & Mem Γ) (StateT Γ <| StateT Δ <| M) :=
  Handler.case
    (Handler.case
      h.lift -- `E`
      (State.handler (M := M)).lift) -- `Mem Δ`
    State.handler -- `Mem Γ`

abbrev State.handler3 (Θ Δ Γ) (h : Handler E M) : Handler (E & Mem Θ & Mem Δ & Mem Γ) (StateT Γ <| StateT Δ <| StateT Θ <| M) :=
  Handler.case
    (Handler.case
      (Handler.case
        h.lift -- `E`
        (State.handler (M := M)).lift) -- `Mem Θ`
      (State.handler (M := StateT Θ M)).lift) -- `Mem Δ`
    State.handler -- `Mem Γ`


@[aesop 10%] theorem State.ite_push_state3 [Decidable c] {t e : (StateT Γ <| StateT Δ <| StateT Θ M) A}
  : (if c then t else e) γ δ θ = (if c then t γ δ θ else e γ δ θ)
  := by split <;> simp_all only

@[aesop 10%] theorem State.bind_push_state3 [Monad M]
  {a : (StateT Γ <| StateT Δ <| StateT Θ M) A}
  {b : A -> (StateT Γ <| StateT Δ <| StateT Θ M) B}
  : (a >>= b) γ δ θ = (a γ δ θ >>= fun res => b res.1.1.1 res.1.1.2 res.1.2 res.2)
  := rfl

@[simp] theorem State.spin_state_irrelevant [Monad M] [Iter M] : (spin : StateT Γ M A) γ = spin := sorry

theorem Functor.map_pure_3 {M : Type -> Type} [Monad M]
  : (Prod.snd ∘ Prod.fst) <$> ((Pure.pure a : (StateT Γ <| StateT Δ <| StateT Θ <| M) A) γ δ θ : M ((((A × Γ) × Δ) × Θ)))
  = return δ
  := by sorry

@[simp] theorem Functor.map_pure_3'
  : (Prod.fst ∘ Prod.snd ∘ Prod.fst) <$> ((Pure.pure () : (StateT Γ <| StateT (ConA [R]) <| StateT Θ <| (ITree E)) Unit) γ (r, ()) θ : (ITree E) ((((Unit × Γ) × [R]) × Θ)))
  = return r
  := by sorry

@[simp] theorem Functor.map_ite [Decidable c] [Functor m] {t e : m a}
  : f <$> (if c then t else e) = if c then (f <$> t) else (f <$> e)
  := apply_ite (Functor.map f) c t e

@[simp] theorem Functor.map_dite [Decidable c] [Functor m] {t e : m a}
  : f <$> (if _ : c then t else e) = if _ : c then (f <$> t) else (f <$> e)
  := apply_ite (Functor.map f) c t e


-- open Lean Qq Meta in
-- /-- This does not perform too well. -/
-- def normConA : Meta.Simp.Simproc := fun e => do
--   withTransparency .default do
--     let_expr interp E A M inst₁ inst₂ h t γ δ θ := e | return .continue
--     -- have A : Q(Ty) := A
--     let Γ : Q(Con) <- mkFreshExprMVarQ q(Con)
--     have γ : Q(ConA $Γ) := γ
--     -- logInfo m!"normConA: γ is {γ}, its type is {<- inferType γ}"
--     let γTy <- inferType γ
--     let .true <- isDefEq q(ConA $Γ) γTy | throwError "normConQ: Could not obtain `{Γ} : Con` from {γTy}, since it is not defEq to {q(ConA $Γ)}."
--     let { γ', prfEq } <- ConA.normalize Γ γ
--     return .done {
--       expr := <- mkAppOptM ``interp #[E, A, M, inst₁, inst₂, h, t, γ', δ, θ]
--       proof? := sorry
--     }
-- simproc_pattern% (interp (M := StateT _ <| StateT _ <| StateT _ <| ITree _) _ _ _ _ _) => normConA


/-
  What follows are a bunch of rules which facilitate symbolic execution.
  These are too specific, as in they are specific to `State.handler3`.
  We should generalize these rules.
-/

-- * Γ
theorem State.exe_Γ_rd {v : Var Γ A} {b : A -> ITree (E & Mem Θ & Mem Δ & Mem Γ) B}
  : interp (State.handler3 (M := ITree E) Θ Δ Γ h) (trigger (.right (Mem.rd v)) >>= b) γ δ θ
  = interp (State.handler3 (M := ITree E) Θ Δ Γ h) (b (γ.get v)) γ δ θ
  := by
    simp only [interp_bind, interp_trigger]
    simp only [State.bind_push_state]
    simp only [State.handler3, Handler.case, Handler.lift, State.handler]
    rw [State.read]
    sorry
theorem State.exe_Γ_wr {v : Var Γ A} {val : A}
  : interp (State.handler3 (M := ITree E) Θ Δ Γ h) (trigger (.right (Mem.wr v val)) >>= b) γ δ θ
  = interp (State.handler3 (M := ITree E) Θ Δ Γ h) (b ()) (γ.set v val) δ θ
  := by sorry

-- * Δ
theorem State.exe_Δ_rd {v : Var Δ A} {b : A -> ITree (E & Mem Θ & Mem Δ & Mem Γ) B}
  : interp (State.handler3 (M := ITree E) Θ Δ Γ h) (trigger (.left <| .right (Mem.rd v)) >>= b) γ δ θ
  = interp (State.handler3 (M := ITree E) Θ Δ Γ h) (b (δ.get v)) γ δ θ
  := by sorry
theorem State.exe_Δ_wr {v : Var Δ A} {val : A}
  : interp (State.handler3 (M := ITree E) Θ Δ Γ h) (trigger (.left <| .right (Mem.wr v val)) >>= b) γ δ θ
  = interp (State.handler3 (M := ITree E) Θ Δ Γ h) (b ()) γ (δ.set v val) θ
  := by sorry
theorem State.exe_Δ_wr_end {v : Var Δ A} {val : A}
  : interp (State.handler3 (M := ITree E) Θ Δ Γ h) (trigger (.left <| .right (Mem.wr v val))) γ δ θ
  = interp (State.handler3 (M := ITree E) Θ Δ Γ h) (return ()) γ (δ.set v val) θ
  := by sorry

-- * Θ
theorem State.exe_Θ_rd {Θ Δ Γ : Con} {θ γ δ} {A: Ty} {B} {E} {h} {b : A -> ITree (E & Mem Θ & Mem Δ & Mem Γ) B} {v : Var Θ A}
  : interp (State.handler3 (M := ITree E) Θ Δ Γ h) (trigger (.left <| .left <| .right (Mem.rd v)) >>= b) γ δ θ
  = interp (State.handler3 (M := ITree E) Θ Δ Γ h) (b (θ.get v)) γ δ θ
  := by sorry
theorem State.exe_Θ_wr {v : Var Θ A} {val : A}
  : interp (State.handler3 (M := ITree E) Θ Δ Γ h) (trigger (.left <| .left <| .right (Mem.wr v val)) >>= b) γ δ θ
  = interp (State.handler3 (M := ITree E) Θ Δ Γ h) (b ()) γ δ (θ.set v val)
  := by sorry

theorem State.exe_ite {Θ Δ Γ : Con} {θ γ δ} {A B} {E} {h} [Decidable c]
  {t e : ITree (E & Mem Θ & Mem Δ & Mem Γ) A} {b : A -> ITree (E & Mem Θ & Mem Δ & Mem Γ) B}
  : interp (State.handler3 (M := ITree E) Θ Δ Γ h) ((if c then t else e) >>= b) γ δ θ
  = (if c
      then interp (State.handler3 (M := ITree E) Θ Δ Γ h) (t >>= b) γ δ θ
      else interp (State.handler3 (M := ITree E) Θ Δ Γ h) (e >>= b) γ δ θ)
  := by split <;> simp_all only
