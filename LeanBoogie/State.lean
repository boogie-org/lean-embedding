import LeanBoogie.Effect.Mem
import LeanBoogie.Iter
import LeanBoogie.ConTy

namespace LeanBoogie

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



/-
  # Interpreting
-/

def handle [Monad M] : Mem Γ Ans -> StateT Γ M Ans
| .rd v => State.read v
| .wr v val => State.write v val

def interp (tm : ITree (Mem Γ) A) : StateT Γ (ITree ∅) A := fun s₀ =>
  ITree.corec (fun ⟨tm, s⟩ =>
    match tm.dest with
    | .ret (.up a) => .ret (.up (a, s))
    | .tau t => .tau (t, s)
    | .vis ⟨Ans, .up ((e : Mem Γ Ans)), (k : ULift Ans -> ITree (Mem Γ) A)⟩ =>
      -- would be nice to use `handle` here instead of the match
      -- let m : StateT Γ (ITree ∅) Ans := handle e
      match e with
      | .rd v => .tau ⟨k (.up (s.get v)), s⟩
      | .wr v val => .tau ⟨k (.up ()), s.set v val⟩
  ) (tm, s₀)

def interp' {E : Type -> Type} (tm : ITree (Mem Γ & E) A) : StateT Γ (ITree E) A := fun s₀ =>
  ITree.corec (fun ⟨tm, s⟩ =>
    match tm.dest with
    | .ret (.up a) => .ret (.up (a, s))
    | .tau t => .tau (t, s)
    | .vis ⟨Ans, .up (.right (e : E Ans    )), k⟩ => .vis ⟨Ans, .up e, fun ans => ⟨k ans, s⟩⟩ -- don't interpret the rest of the effects.
    | .vis ⟨Ans, .up (.left  (e : Mem Γ Ans)), (k : ULift Ans -> ITree (Mem Γ & E) A)⟩ =>
      match e with
      | .rd v => .tau ⟨k (.up (s.get v)), s⟩
      | .wr v val => .tau ⟨k (.up ()), s.set v val⟩
  ) (tm, s₀)

-- Ideally we want something as general as this:
-- def interp'' {E : Type -> Type} [inst : HasEff (Mem Γ) E] (tm : ITree E A) : StateT Γ (ITree inst.Strip) A := fun s₀ =>
--   ITree.corec (fun ⟨tm, s⟩ =>
--     match tm.dest with
--     | .ret (.up a) => .ret (.up (a, s))
--     | .tau t => .tau (t, s)
--     | .vis ⟨Ans, .up ((e : E Ans    )), k⟩ =>
--       inst.elim (fun e =>
--         match e with
--         | .rd v => .tau ⟨k (.up (s.get v)), s⟩
--         | .wr v val => .tau ⟨k (.up ()), s.set v val⟩
--       ) (fun e => .vis e k) e
--   ) (tm, s₀)

theorem interp_pure : interp (pure a : ITree (Mem Γ) A) = pure a := sorry

theorem interp_bind {ta : ITree (Mem Γ) A} {tb : A -> ITree (Mem Γ) B}
  : interp (ta >>= tb) = (interp ta) >>= (fun a => interp (tb a))
  := sorry

-- /-- Convenience mix of `interp_bind` and `bind_state_pull`. -/
theorem interp_bind_pull {ta : ITree (Mem Γ) A} {tb : A -> ITree (Mem Γ) B}
  : interp (bind ta tb) s = bind (interp ta s) (fun x => interp (tb x.1) x.2)
  := sorry

theorem interp_iter {f : A -> ITree (Mem Γ) (A ⊕ B)} {a₀ : A}
  : interp (iter f a₀) = iter (fun (a : A) => interp (f a)) a₀
  := sorry

theorem interp_read {v : Var Γ A} : interp (Mem.read v) = State.read v := sorry
theorem interp_write {v : Var Γ A} : interp (Mem.write v val) = (State.write v val) := sorry
theorem interp_ite [Decidable φ] : interp (if φ then t else e) = (if φ then interp t else interp e) := sorry

#check Classical.byContradiction
