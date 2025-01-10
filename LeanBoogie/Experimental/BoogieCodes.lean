import Lean
import Std.Data.HashMap
import Std.Data.HashSet
import Qq
import ITree
import LeanBoogie.ConTy
import LeanBoogie.State

open Std (HashMap HashSet)
open ITree
abbrev POption (P : Prop) : Type := Option (PLift P)

namespace LeanBoogie

/-
  # Deep Embedding of Boogie
  We have seen `Con`, `Ty`, which is a deep embedding of only types.
  This seeks to provide `Term` and `Prog` as well, in a similar spirit to `Con`, and `Ty`.
-/

/-- Terms cant have effects. -/
inductive Term : Con -> Ty -> Type
| add : Term Γ .int -> Term Γ .int -> Term Γ .int
| mul : Term Γ .int -> Term Γ .int -> Term Γ .int
| lit {A : Ty} : A -> Term Γ A
| var : (v : Var Γ A) -> Term Γ A
| app : Term Γ (.map A B) -> Term Γ A -> Term Γ B
| lam : (A : Ty) -> Term (A :: Γ) B -> Term Γ (.map A B)

inductive Formula : Con -> Type
| eq : Term Γ A -> Term Γ A -> Formula Γ
| le : Term Γ .int -> Term Γ .int -> Formula Γ
| forallE : (A : Ty) -> Formula (A :: Γ) -> Formula Γ

-- Or split this up into `Command` and then `Prog := List Command`
inductive Prog : Con -> Type
| skip : Prog Γ
| seq : Prog Γ -> Prog Γ -> Prog Γ
| assign : (v : Var Γ A) -> Term Γ A -> Prog Γ
| assume : Formula Γ -> Prog Γ
| ite : (c : Term Γ .bool) -> (t : Prog Γ) -> (e : Prog Γ) -> Prog Γ
| loop : (c : Term Γ .bool) -> (body : Prog Γ) -> Prog Γ

def Prog.isSkip : Prog Γ -> Bool
| .skip => true
| _ => false

def Prog.seqMany : List (Prog Γ) -> Prog Γ
| [] => .skip
| c :: cs => .seq c (seqMany cs)

abbrev State (Γ : Con) : Type := go Γ 0 (Nat.zero_lt_succ (List.length Γ))
where go (Γ : Con) (n : Nat) (_ : n < Γ.length + 1) : Type :=
  if h : n = Γ.length then Unit
  else Term Γ Γ[n] × go Γ (n+1) (by omega)

#reduce (types := true) State [.int, .int]
#reduce (types := true) ConA [.int, .int]

def State.set (γ : State Γ) (v : Var Γ A) (val : Term Γ A) : State Γ := sorry

def Term.normalize : Term Γ A -> Term Γ A
| .add x y => sorry
| _ => sorry

def State.normalize : State Γ -> State Γ := sorry

def Prog.step (p : Prog Γ) : StateT (State Γ) Id (Prog Γ) :=
  match p with
  | .assign (A := A) v val => fun γ => (.skip, γ.set v val)
  | _ => sorry

def Prog.run (p : Prog Γ) : StateT (State Γ) (ITree ∅) Unit := do
  Iter.iter (fun p => if p.isSkip then return .inr () else return .inl p) p



/-
  # Interpretation
-/

def TermA : Term Γ A -> ITree (Mem Γ) A
| .var v => Mem.read v
| .add a b => do return (<- TermA a) + (<- TermA b)
| .app f a => do return (<- TermA f) (<- TermA a)
| _ => sorry

def StateA : State Γ -> ConA Γ := sorry

def ProgA : Prog Γ -> ITree (Mem Γ) Unit
| .skip => return ()
| .seq a b => do ProgA a; ProgA b
| .assign v e => do
  let val <- TermA e
  Mem.write v val
| _ => sorry

def VC : Prog Γ -> Prop := sorry

theorem Term.normalize_correct : {t : Term Γ A} -> TermA t = TermA (Term.normalize t)
| .add x y => sorry
| _ => sorry

theorem State.normalize_correct : {γ : State Γ} -> StateA γ = StateA (State.normalize γ) := sorry

-- example {p : Prog Γ} {P : _ -> Prop} : P (Prog.run p) -> P (interp h <| ProgA p) := by
theorem Prog.run_eq_interp_ProgA {p : Prog Γ} : (Prog.run p) = (interp h <| ProgA p) := by
  -- `h : Handler (Mem Γ) (StateT (State Γ) (ITree ∅))`, as opposed to
  --     `Handler (Mem Γ) (StateT (ConA Γ)  (ITree ∅))`.
  -- `State Γ           = Term Γ .int × Term Γ .int × Unit`, as opposed to
  -- `ConA [.int, .int] = Int         × Int         × Unit`,
  -- meaning that we have the concrete representation of the values in object language,
  -- and therefore can do all kinds or processing or symbolic execution without needing to use
  -- Lean's metaprogramming.
  -- We can do this processing without having a concrete program, since we can pattern match on `Term`.
  sorry

def p1 : Prog [.int, .int, .int] := Prog.seqMany [
  .assign .v0 (.lit 123),
  .assign .v1 (.lit 456),
  .assign .v0 (.add (.var .v1) (.var .v2)),
  .loop (.lit true) <| Prog.seqMany [
    .assign .v0 (.add (.var .v0) (.lit 1))
  ]
]

example {h : Handler (Mem [.int, .int, .int]) (StateT (State [.int, .int, .int]) (ITree ∅))}
  : interp h (ProgA p1) = interp h (ProgA p2)
  := by
  rw [p1]
  -- need to relate `State Γ` and `ConA Γ`, where the former has many representations of the same `ConA Γ`.
  rw [<- Prog.run_eq_interp_ProgA]

  ext γ
  dsimp [StateT.run]

  /- Now you have `p.run γ`, which we can execute symbolically by invoking the non-meta `Term.normalize` function from meta code.
    `Term.normalize` does the same thing as my `normConA`, except it is:
    1. A lot easier to implement, because you work on `Term Γ A` and not `Lean.Expr`
    2. Easier to reason about: You get definitional equalities, you *can* prove `Term.normalize_correct`.

    Next steps: We want to interpret `State Γ` into `ConA Γ` at the very high level using `StateA`,
    so `p.run γ` becomes `p.run (StateA γ)`, which we can rewrite into `p.run (StateA γ.normalize)`
    using `State.normalize_correct`, and now we can evaluate `γ.normalize`, which is an operation
    on the object-level AST. We can call this from the meta level.
  -/
  sorry

/- Instead of denoting everything (including `Term`) into `ITree`, we could choose to denote into
  a pure expression instead.
  We still have to denote `Prog` into an ITree (duh), but at least terms would be pure.
  ```
  def TermA : Term Γ A -> Γ -> A
  | .var v, γ => γ.get v
  | .add a b, γ => TermA a γ + TermA b γ
  | .app f a, γ => TermA f γ (TermA a γ)
  | _, γ => sorry

  def FormulaA : Formula Γ -> Γ -> Prop
  | .eq a b, γ => TermA a γ = TermA b γ
  | .forallE A B, γ => ∀a : A, FormulaA B (a, γ)
  | _, γ => sorry

  def ProgA : Prog Γ -> ITree _ Unit
  ```
-/
