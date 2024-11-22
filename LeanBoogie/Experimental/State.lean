import LeanBoogie.ITree.ITree

/-
  # State in Boogie
-/

-- ## Codes for boogie state types

inductive Ty : Type
| bool
| int
| bv (bits : Nat)
-- | map (A B : Ty)

abbrev Con : Type := List Ty
-- inductive Con : Type where
-- | empty : Con
-- | ext : Con -> Ty -> Con

-- def Var (Γ : Con) : Type := Fin Γ.length
inductive Var : (Γ : Con) -> (A : Ty) -> Type
| vz :            Var (A :: Γ) A
| vs : Var Γ A -> Var (B :: Γ) A

-- ## Interpretations of boogie type codes

def TyA : Ty -> Type
| .int => Int
| .bool => Bool
| .bv bits => BitVec bits
-- | .map A B => TyA A -> TyA B

def ConA : Con -> Type
| [] => Unit
| x :: xs => TyA x × ConA xs

instance : CoeSort Ty Type := ⟨TyA⟩
instance : CoeSort Con Type := ⟨ConA⟩

-- ## Interaction Tree Events for State

namespace Approach1
  inductive Mem (Γ : Con) : /- Type -> -/ Type where
  | rd : Var Γ A          -> Mem Γ /- (TyA A) -/
  | wr : Var Γ A -> TyA A -> Mem Γ /- Unit -/
  -- def Mem.read  (v : Var Γ A)           : ITree (Mem Γ) A := .vis (.rd v) (fun a:A => .ret a)
  -- def Mem.write (v : Var Γ A) (val : A) : ITree (Mem Γ) A := .vis (.wr v val) (fun () => .ret ())
end Approach1

namespace Approach2
  inductive Mem (Γ : Type) : /- (A:Type) -> -/ Type where
  | rd (π : Γ -> Ans) : Mem Γ /- A -/
  | wr (δ : Γ -> Ans -> Γ) : Mem Γ /- Unit -/
end Approach2
