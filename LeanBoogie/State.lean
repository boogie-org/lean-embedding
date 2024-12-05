import LeanBoogie.Mem
import LeanBoogie.Iter

namespace LeanBoogie

/-
  The file `Mem.lean` only defines the `Mem` effect, but lacks any interpretation.
  We give one interpretation here.

  You can imagine giving a completely different model for memory events in a world without
  strong consistency guarantees. I have no idea how that would look like, but it would
  be very interesting to try.
-/

/-
  # The state monad
-/

/-- E.g. `ConA [.int, .bv 32] ≣ Unit × Int × BitVec 32`. -/
abbrev ConA : Con -> Type
| [] => Unit
| x :: xs => TyA x × ConA xs

instance : CoeSort Con Type := ⟨ConA⟩

set_option linter.unusedVariables false in
/-- Read a variable's value from the state. -/
def ConA.get : {Γ : Con} -> Γ -> Var Γ A -> A
| _ :: _, (x, _), .vz   => x
| _ :: _, (_, γ), .vs v => γ.get v

set_option linter.unusedVariables false in
/-- Set a variable's value, returning an updated state.
  Example: `γ.set v 123 : Γ`.  -/
def ConA.set : {Γ : Con} -> Γ -> Var Γ A -> A -> Γ
| _ :: _, (_, γ), .vz  , a' => (a', γ)
| _ :: _, (a, γ), .vs v, a' => (a, γ.set v a')

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

  The above `interp_*` lemmas show that `interp` is a monad morphism.
  We should also show properties about the interpreted state, which we can not show on the `Mem` events.
  For example, last write wins, etc.
-/

/- ### Normal form of `ConA`
  Given a starting `γ : ConA Γ` and `γ' = γ.update |>.update .. |>.update ... |> ...`,
  we can normalize these into essentially `γ' = { #0 := ...γ..., #1 := ...γ..., #2 := ...γ..., ...}`.

  - We should eventually have a tactic which performs this normalization in a performant way.
  - We should eventually have a delaborator which can render states `γ : ConA Γ` in a more
    human-readable way.
-/

@[simp] theorem ConA.update_lww {Γ : Con} {v : Var Γ A} {γ : Γ} : (γ.set v a').set v a'' = γ.set v a'' := sorry
@[simp] theorem ConA.update_get {Γ : Con} {v : Var Γ A} {γ : Γ} : (γ.set v a').get v = a' := by
  induction Γ with
  | nil => cases v
  | cons B Γ ih =>
    cases v with
    | vz => rfl
    | vs v => simp only [get, ih]
-- more theorems








/-
  # Interpreting
-/

def interp (tm : ITree (Mem Γ) A) : StateT Γ (ITree ∅) A := fun s₀ =>
  ITree.corec (fun ⟨tm, s⟩ =>
    match tm.dest with
    | .ret (.up a) => .ret (.up (a, s))
    | .tau t => .tau (t, s)
    | .vis ⟨Ans, .up ((e : Mem Γ Ans)), (k : ULift Ans -> ITree (Mem Γ) A)⟩ =>
      match e with
      | .rd v => .tau ⟨k (.up (s.get v)), s⟩
      | .wr v val => .tau ⟨k (.up ()), s.set v val⟩
  ) (tm, s₀)

def interp' {E : Type -> Type} (tm : ITree (E & Mem Γ) A) : StateT Γ (ITree E) A := fun s₀ =>
  ITree.corec (fun ⟨tm, s⟩ =>
    match tm.dest with
    | .ret (.up a) => .ret (.up (a, s))
    | .tau t => .tau (t, s)
    | .vis ⟨Ans, .up (.left  (e : E Ans    )), k⟩ => .vis ⟨Ans, .up e, fun ans => ⟨k ans, s⟩⟩ -- don't interpret the rest of the effects.
    | .vis ⟨Ans, .up (.right (e : Mem Γ Ans)), (k : ULift Ans -> ITree (E & Mem Γ) A)⟩ =>
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



-- ## Example:

structure Global_ where
  i : Int
  n : BitVec 32

def Global.Γ : Con := [.int, .bv 32]
abbrev Global : Type := Global.Γ
abbrev Global.i (γ : Global) : Int       := γ.get .vz
abbrev Global.n (γ : Global) : BitVec 32 := γ.get (.vs .vz)

#check Global_.i
#check Global.i
