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

set_option linter.unusedVariables false in
def ConA.get : {Γ : Con} -> Γ -> Var Γ A -> A
| _ :: _, (x, _), .vz   => x
| _ :: _, (_, γ), .vs v => γ.get v

set_option linter.unusedVariables false in
def ConA.update : {Γ : Con} -> Γ -> Var Γ A -> A -> Γ
| _ :: _, (_, γ), .vz  , a' => (a', γ)
| _ :: _, (a, γ), .vs v, a' => (a, γ.update v a')

/- ### Normal form of `ConA`
  Given a starting `γ : ConA Γ` and `γ' = γ.update |>.update .. |>.update ... |> ...`,
  we can normalize these into essentially `γ' = { #0 := ...γ..., #1 := ...γ..., #2 := ...γ..., ...}`
  We should have a tactic which performs this normalization in a performant way.
-/
@[simp] theorem ConA.update_lww {Γ : Con} {v : Var Γ A} {γ : Γ} : (γ.update v a').update v a'' = γ.update v a'' := sorry
@[simp] theorem ConA.update_get {Γ : Con} {v : Var Γ A} {γ : Γ} : (γ.update v a').get v = a' := by
  induction Γ with
  | nil => cases v
  | cons B Γ ih =>
    cases v with
    | vz => rfl
    | vs v => simp only [get, ih]
-- more theorems

-- ## Interaction Tree Events for State

inductive Mem (Γ : Con) : Type -> Type where
| rd : Var Γ A          -> Mem Γ A
| wr : Var Γ A -> TyA A -> Mem Γ Unit

def Mem.read  (v : Var Γ A)           : ITree (Mem Γ) A    := .vis (.rd v    ) (fun (a : A) => .ret a)
def Mem.write (v : Var Γ A) (val : A) : ITree (Mem Γ) Unit := .vis (.wr v val) (fun () => .ret ())

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

def Empty' : Type -> Type := fun _ => Empty

inductive Plus (E₁ E₂ : Type -> Type) : Type -> Type
| left  : E₁ X -> Plus E₁ E₂ X
| right : E₂ X -> Plus E₁ E₂ X

instance : HAdd (Type -> Type) (Type -> Type) (Type -> Type) := ⟨Plus⟩

def merge : ITree (Mem Γ + Mem Δ) A -> ITree (Mem (Γ ++ Δ)) A := sorry

def interp : ITree (Mem Γ) Unit -> StateT (ConA Γ) (ITree Empty') Unit := sorry
