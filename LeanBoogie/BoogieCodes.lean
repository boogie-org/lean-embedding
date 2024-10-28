import LeanBoogie.DijkstraMonad
import LeanBoogie.ITree
import Lean
import Qq

open Std (HashMap HashSet)

namespace Boog

-- # Syntax

-- ## Boogie Types

inductive BType : Type where
| unit : BType
| int : BType
| bool : BType
| map : BType -> BType -> BType

abbrev denoteType : BType -> Type
| .unit => Unit
| .bool => Bool
| .int => Int
| .map A B => denoteType A -> denoteType B

instance : CoeSort BType Type := ⟨denoteType⟩

notation "⟦" A "⟧" => denoteType A
notation A " ~~> " B => BType.map A B

-- inductive BProc : Type
-- | ty : BType -> BProc
-- | map : BType -> BProc -> BProc
-- instance : Coe (BType) (BProc) where coe := .ty
-- abbrev denoteProc (M : Type -> Type) : BProc -> Type
-- | .ty A => denoteType A
-- | .map A B => denoteType A -> denoteProc M B


-- ## Context

structure Context : Type where
  /-- Set of variable names. -/
  Var : Finset String
  varTypes : (v : Var) -> BType

  Fix : Finset String
  fixTypes : (f : Fix) -> (BType × BType)
  /-- We remember which var(s) we want to be decreasing. -/
  fixWf : (f : Fix) -> (v : Var) ×' (r : (varTypes v) -> (varTypes v) -> Prop) ×' WellFounded r
abbrev FreshFix (Γ : Context) : Type := (f : String) ×' f ∉ Γ.Fix

/- Or maybe just use de brujin, or hashmaps... -/
abbrev Context.extFix (Γ : Context) (f : FreshFix Γ) (v : Γ.Var) (C : BType) (r : (Γ.varTypes v) -> (Γ.varTypes v) -> Prop) (wf : WellFounded r) : Context :=
  { Γ with
    Fix := insert f.1 Γ.Fix
    fixTypes := fun f' =>
      if h : f' = f.1
        then (Γ.varTypes v, C)
        else
          have : insert f.1 Γ.Fix = Γ.Fix := by sorry
          Γ.fixTypes (this ▸ f')
    fixWf := fun f' =>
      if h : f' = f.1
        then ⟨v, r, wf⟩
        else
          have : insert f.1 Γ.Fix = Γ.Fix := by sorry
          Γ.fixWf (this ▸ f')
  }

/-
  ## Boogie Programs and Expressions
  Usually this is split up into `Stmt` and `Expr` but keeping it in one makes if-expressions easier.
-/

mutual
  -- inductive BoogieProp : Context -> Type
  -- | le : Boogie Γ A -> Boogie Γ A -> BoogieProp Γ
  -- | eq : Boogie Γ A -> Boogie Γ A -> BoogieProp Γ
  -- -- | forallE : (v : String) -> v ∉ Γ.Var -> (A : BType) -> BoogieProp (Γ.ext v A) -> BoogieProp Γ

  inductive Boogie : Context -> BType -> Type
  | skip : Boogie Γ .unit
  | seq : Boogie Γ .unit -> Boogie Γ .unit -> Boogie Γ .unit
  | assign : (v : Γ.Var) -> Boogie Γ (Γ.varTypes v) -> Boogie Γ .unit
  -- /-- You can't really have `assume`... that effectively results in a partial function. -/
  -- | assume : BoogieProp Γ -> Boogie Γ .unit
  | ite : (c : Boogie Γ .bool) -> (t : Boogie Γ A) -> (e : Boogie Γ A) -> Boogie Γ A
  | add : Boogie Γ .int -> Boogie Γ .int -> Boogie Γ .int
  | mul : Boogie Γ .int -> Boogie Γ .int -> Boogie Γ .int
  | lit : Int -> Boogie Γ .int
  /-- Read a var. -/
  | var : (v : Γ.Var) -> Boogie Γ (Γ.varTypes v)

  -- ? Fixpoints declare an additional local variable which can be called to recurse.
  | fix (f : FreshFix Γ) (v : Γ.Var)
    (r : (Γ.varTypes v) -> (Γ.varTypes v) -> Prop)
    (wf : WellFounded r)
    (body : Boogie (Γ.extFix f v (Γ.varTypes v) r wf) (.map (Γ.varTypes v) C))
    : Boogie Γ (.map (Γ.varTypes v) C)

  | app : Boogie Γ (.map A B) -> Boogie Γ A -> Boogie Γ B
end

#check WellFounded.fix

-- # Denotational Semantics

-- abbrev denoteContext (Γ : Context) : Type := (v : Γ.Var) -> denoteType (Γ.varTypes v h)
abbrev denoteContext (Γ : Context) : Type := (v : Γ.Var) -> denoteType (Γ.varTypes v)
instance : CoeSort Context Type := ⟨denoteContext⟩
notation "⟦" Γ "⟧" => denoteContext Γ


abbrev bM (Γ : Context) : BType -> Type
| .unit => StateM Γ Unit
| .bool => StateM Γ Bool
| .int => StateM Γ Int
| .map A B => A -> bM Γ B

def bM.bind (a : bM Γ A) (b : bM Γ (.map A B)) : bM Γ B :=
  match B with
  | .map C D => by
    simp [bM] at b
    rw [bM]
    exact fun c =>
      let ih := bM.bind
      sorry
  | .int => by
    rw [bM]
    rw [bM] at b
    sorry
  | _ => sorry

abbrev denote : {A : BType} -> Boogie Γ A -> bM Γ A
| .unit, .skip => pure ()
| .int, .lit i => pure i
| .unit, .assign v e => do
  match hv : (Γ.varTypes v) with
  | .map A B => sorry
  | .int =>
    let val := hv ▸ (<- denote (hv ▸ e))
    modify fun (state : Γ) w =>
      if h : w = v
        then h ▸ val
        else state w
  | _ => sorry
| .unit, .seq p₁ p₂ => do
  denote p₁
  denote p₂
| B, Boogie.app (A := A) f a => bM.bind a f
| _, .ite c t e => do
  if <- denote c
    then denote t
    else denote e
| _, .var v => do
  let st <- get
  return st v
| _, .mul x y => do
  let x <- denote x
  let y <- denote y
  return x * y
| _, .add x y => do
  let x <- denote x
  let y <- denote y
  return x + y
| .map _ _, @Boogie.fix _ C f v r wf body => do
  -- When you call functions, you may have to allocate a new stack frame. This translates into adding a state monad onto the monad stack.
  let m : Γ -> Γ.extFix f v (Γ.varTypes v) r wf := id -- ...except adding a fixpoint function to the context carries no runtime data, so it's just the same.
  have h : denoteContext Γ = denoteContext (Γ.extFix f v (Γ.varTypes v) r wf) := rfl
  let (m_body, γ') := StateT.run (denote body) (h ▸ (<- get)) -- ! `m_body : A -> B`, already denoted, which isn't able to have effects :(
  let m : StateM Γ _ := @WellFounded.fix (Γ.varTypes v) (fun _ => C) r wf fun x R =>
    -- * Here you want to denote body, for which you need to give it R....
    -- * So you need a way to call functions in the boogie syntax.
    -- * And when you call, you allocate a new "stack frame"
    sorry
  sorry
-- | Boogie.call
-- | _ => sorry

#check 1

-- # Examples

-- John's suggestion:
-- inductive P : State -> State -> Prop

def exampleWithAssume {Γ : Context} (x : Int) : (x > 0) -> StateM Γ Int :=
  fun _h => -- assume x > 0 -- * bubble these up, maybe along context.
    return 10 / x
