import LeanBoogie.ITree
-- import LeanBoogie.Boogie
import Mathlib.Data.Real.Basic

namespace LeanBoogie
open ITree (HasEff)

/-
  # Memory (Effects) in Boogie

  Without interpretation yet. For that, look into `State.lean`.
-/

-- ## Codes for boogie state types

/-- Codes for Boogie types.

  An alternative formulation would be forgo `Ty` entirely and define `def Con : Type 1 := List Type`,
  which would allow for arbitrary types.
-/
inductive Ty : Type
/-- Booleans. Interpreted as `Bool`.
  Note: Lean has `Prop` which would make more sense to use for anything formula-related. -/
| bool : Ty
-- /-- Propositions? Interpreted as `Prop`. Not sure if this is a good idea. -/
-- | prop : Ty
/-- Unbounded integers. Interpreted as `ℤ`. -/
| int : Ty
/-- Real numbers. Interpreted as `ℝ`. -/
| real : Ty
/-- Bitvectors. Interpreted as `BitVec n`. -/
| bv (bits : Nat) : Ty
/-- Boogie maps. These get interpreted as function types.

  Note: Since Lean functions are *extensional*, so are Boogie maps in our rendition.
  However, the [Boogie 2 spec](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml178.pdf)
  says that maps are not extensional, due to [a Dafny issue](https://github.com/dafny-lang/dafny/issues/2463).
  We choose to ignore this, for now. -/
| map (A B : Ty) : Ty
infixl:20 " ~> " => Ty.map

/-- Context, assigns every variable (de-Brujin indexed) its type code.

  For example, `def Γ : Con := [.int, .int ~> .int]`.

  An alternative formulation of `Con` could be
  `def Con : Type := (Names : Finset String) × (types : Names -> Ty)`.
-/
abbrev Con : Type := List Ty
-- inductive Con : Type where
-- | empty : Con
-- | ext : Con -> Ty -> Con

/-- Variables, referring to an entry in a context. This is essentially `Fin Γ.length`,
  but also asserts that the variable at that index has type `A`, which is often nicer to deal with.  -/
inductive Var : (Γ : Con) -> (A : Ty) -> Type
| vz :            Var (A :: Γ) A
| vs : Var Γ A -> Var (B :: Γ) A

/-- Interprets e.g. `Ty.int` into `Int`. -/
abbrev TyA : Ty -> Type
| .int => Int
| .real => Real
| .bool => Bool
| .bv bits => BitVec bits
| .map A B => TyA A -> TyA B

-- So that you can do e.g. `(my_int : .int) -> ...` instead of `(my_int : TyA .int) -> ...`.
instance : CoeSort Ty Type := ⟨TyA⟩


-- ## `Mem` Effect

inductive Mem (Γ : Con) : Type -> Type where
| rd : Var Γ A          -> Mem Γ A
| wr : Var Γ A -> TyA A -> Mem Γ Unit

def Mem.read  (v : Var Γ A)           : ITree (Mem Γ) A    := .vis (.rd v    ) .ret
def Mem.write (v : Var Γ A) (val : A) : ITree (Mem Γ) Unit := .vis (.wr v val) .ret

def Mem.read'  (v : Var Γ A)           : ITree (E & Mem Γ) A    := .vis (Mem.rd v    ) .ret
def Mem.write' (v : Var Γ A) (val : A) : ITree (E & Mem Γ) Unit := .vis (Mem.wr v val) .ret

-- the most general form is like this, with `HasEff`:
def Mem.read''  [HasEff (Mem Γ) E] (v : Var Γ A)           : ITree E A    := .vis (Mem.rd v    ) .ret
def Mem.write'' [HasEff (Mem Γ) E] (v : Var Γ A) (val : A) : ITree E Unit := .vis (Mem.wr v val) .ret

def Γ : Con := [.int]
#synth HasEff (Mem Γ) (Mem Γ)

example : ITree (Mem Γ) Unit := do
  Mem.write .vz 123
  return ()

def merge : ITree (Mem Γ & Mem Δ) A -> ITree (Mem (Γ ++ Δ)) A := sorry
