import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import LeanBoogie.Util
import LeanBoogie.TraceClasses

namespace LeanBoogie

/- # Codes for Boogie types

-/

/-- Codes for Boogie types.

  An alternative formulation would be forgo `Ty` entirely and define `def Con : Type 1 := List Type`,
  which would allow for arbitrary types.
-/
@[aesop unsafe cases 1%]
inductive Ty /- (Ptr : Type) -/ : Type
| unit : Ty
/-- Booleans. Interpreted as `Bool`. -/
| bool : Ty
/-- Unbounded integers. Interpreted as `ℤ`. -/
| int : Ty
/-- Real numbers. Interpreted as `ℝ`.  -/
| real : Ty
/-- Bitvectors. Interpreted as `BitVec n`. -/
| bv (bits : Nat) : Ty
/-- Boogie maps. These get interpreted as function types.

  Note: Since Lean functions are *extensional*, so are Boogie maps in our rendition.
  However, the [Boogie 2 spec](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml178.pdf)
  says that maps are not extensional, due to [a Dafny issue](https://github.com/dafny-lang/dafny/issues/2463).
  We choose to ignore this, for now. -/
| map (A B : Ty) : Ty
deriving Repr, DecidableEq
infixl:20 " ~> " => Ty.map

abbrev Ty.bv64 : Ty := .bv 64
abbrev Ty.bv32 : Ty := .bv 32
abbrev Ty.bv16 : Ty := .bv 16
abbrev Ty.bv8 : Ty := .bv 8
abbrev Ty.bv1 : Ty := .bv 1

/-- Interprets e.g. `Ty.int` into `Int`. -/
abbrev TyA : Ty -> Type
| .unit => Unit
| .int => Int
| .real => Real
| .bool => Bool
| .bv bits => BitVec bits
| .map A B => TyA A -> TyA B

-- So that you can do e.g. `(my_int : .int) -> ...` instead of `(my_int : TyA .int) -> ...`.
instance : CoeSort Ty Type := ⟨TyA⟩

def TyA.inhabited : {A : Ty} -> A
| .unit => default
| .int => default
| .real => default
| .bool => default
| .bv _ => default
| .map _ _ => fun _ => inhabited

instance : Inhabited (TyA A) := ⟨TyA.inhabited⟩


/-- Context, assigns every variable (de-Brujin indexed) its type code.

  For example, `def Γ : Con := [.int, .int ~> .int]`.

  An alternative formulation of `Con` could be
  `def Con : Type := (Names : Finset String) × (types : Names -> Ty)`.
-/
abbrev Con : Type := List Ty

/-- Variables, referring to an entry in a context. This is essentially `Fin Γ.length`,
  but also asserts that the variable at that index has type `A`, which is often nicer to deal with. -/
@[aesop unsafe cases 5%]
inductive Var : (Γ : Con) -> (A : Ty) -> Type
| vz :            Var (A :: Γ) A
| vs : Var Γ A -> Var (B :: Γ) A
deriving Repr, DecidableEq

abbrev Var.v0 : Var (A :: Γ) A := .vz
abbrev Var.v1 : Var (B :: A :: Γ) A := .vs .vz
abbrev Var.v2 : Var (C :: B :: A :: Γ) A := .vs (.vs .vz)
abbrev Var.v3 : Var (D :: C :: B :: A :: Γ) A := .vs (.vs (.vs .vz))

@[aesop safe] theorem Var.empty_False (v : Var [] A) : False := by cases v
@[aesop safe] theorem Var.neq_neq_Ty {v : Var Γ A} {v' : Var Γ B} (h : A ≠ B) : ¬HEq v v' := by
  intro h'
  induction Γ with
  | nil => cases v
  | cons C Γ ih =>
    sorry -- cases v, cases v'
theorem Var.heq_same_Ty {Γ} (v₁ : Var Γ A) (v₂ : Var Γ B) : HEq v₁ v₂ -> A = B := by
  sorry

instance Var.decEq : DecidableEq (Var Γ A) := inferInstance
instance Var.decHEq (v₁ : Var Γ A) (v₂ : Var Γ B) : Decidable (HEq v₁ v₂) :=
  if hTy : A = B then (by cases hTy; simp_all only [heq_eq_eq]; exact Var.decEq v₁ v₂)
  else .isFalse (Var.neq_neq_Ty hTy)

def Var.ofIdx : {Γ : Con} -> (i : Fin Γ.length) -> Var Γ Γ[i]
| _ :: _, ⟨.zero, _⟩ => .vz
| _ :: _, ⟨.succ n, h⟩ => .vs (Var.ofIdx ⟨n, Nat.succ_lt_succ_iff.mp h⟩)

set_option linter.unusedVariables false in
def Var.split : {Γ Δ : Con} -> Var (Γ ++ Δ) A -> Var Γ A ⊕ Var Δ A
|        [], Δ, v     => .inr v
| .(A) :: Γ, Δ, .vz   => .inl .vz
|   B  :: Γ, Δ, .vs v => match Var.split v with
                         | .inl v => .inl v.vs
                         | .inr v => .inr v

set_option linter.unusedVariables false in
def Var.merge : {Γ Δ : Con} -> Var Γ A ⊕ Var Δ A -> Var (Γ ++ Δ) A
| Γ, Δ, .inl v => sorry
| Γ, Δ, .inr v => sorry

-- theorem Var.split_merge : split ∘ merge = id := sorry

abbrev Con.dropImpl : (n : Nat) -> (Γ : Con) -> n < Γ.length + 1 -> Con
| 0  , Γ     , _ => Γ
| n+1, _ :: Γ, h => Con.dropImpl n Γ (Nat.succ_lt_succ_iff.mp h)
termination_by structural n _Γ _h => n
abbrev Con.drop (Γ : Con) (n : Fin (Γ.length + 1)) : Con := dropImpl n.1 Γ n.2
-- The following should hold definitionally!
theorem Con.drop_0 : Con.drop Γ ⟨0, h⟩ = Γ := rfl
theorem Con.drop_1 : Con.drop (A :: Γ) ⟨1, h⟩ = Γ := rfl

/-- E.g. `ConA [.int, .bv 32] ≣ Unit × Int × BitVec 32`. -/
abbrev ConA : Con -> Type
| [] => Unit
| x :: xs => TyA x × ConA xs

instance : CoeSort Con Type := ⟨ConA⟩
def ConA.inhabited : {Γ : Con} -> Γ
| [] => Unit.unit
| _ :: _ => (default, inhabited)
instance : Inhabited (ConA Γ) := ⟨ConA.inhabited⟩

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

set_option linter.unusedVariables false in
/-- For example `(a, b, ()) ++ (c, d, ()) = (a, b, c, d, ())`. -/
def ConA.append : {Γ : Con} -> {Δ : Con} -> Γ -> Δ -> (Γ ++ Δ)
|     [], Δ,     (), δ => δ
| A :: Γ, Δ, (a, γ), δ => (a, append γ δ)
instance {Γ Δ : Con} : HAppend Γ Δ (Γ ++ Δ) := ⟨ConA.append⟩

set_option linter.unusedVariables false in
def ConA.dropImpl {Γ : Con} (γ : Γ) : (n : Nat) -> (h : n < Γ.length + 1) -> Con.dropImpl n Γ h
| 0, _ => γ
| n+1, h =>
  let .cons A Γ := Γ
  let (a, γ) := γ
  ConA.dropImpl γ n (Nat.succ_lt_succ_iff.mp h)
termination_by structural n => n
abbrev ConA.drop {Γ : Con} (γ : Γ) (n : Fin (Γ.length + 1)) : Γ.drop n := dropImpl γ n.1 n.2
example {γ : ConA Γ} : γ.drop 0 = γ := rfl -- definitional equality!
example {γ : ConA Γ} (a : TyA A) : @Eq (ConA Γ) (ConA.drop (Γ := (A :: Γ)) (a, γ) 1) γ := rfl -- definitional equality!


/-
  ## Equational reasoning rules for states `γ : ConA Γ`
-/

/-- Last write wins. -/
@[simp] theorem ConA.lww {Γ : Con} {v : Var Γ A} {γ : ConA Γ} : (γ.set v val₁).set v val₂ = γ.set v val₂ := by
  induction Γ with
  | nil => cases v
  | cons B Γ ih =>
    cases v with
    | vz => rfl
    | vs v => simp only [get, set, ih]

@[simp] theorem ConA.get_set {Γ : Con} {v : Var Γ A} {γ : Γ} : (γ.set v val).get v = val := by
  induction Γ with
  | nil => cases v
  | cons B Γ ih =>
    cases v with
    | vz => rfl
    | vs v => simp only [get, ih]

@[aesop unsafe 10%] theorem ConA.get_set' {Γ : Con} {v₁ v₂ : Var Γ A} {γ : Γ} (h : v₁ = v₂)
  : (γ.set v₁ val).get v₂ = val
  := by cases h; exact get_set

/-- We can ignore a `set` if we're setting a different variable from the one we're reading. -/
@[aesop unsafe 10%] theorem ConA.get_set_irrelevant {Γ : Con} {γ : Γ} (v₁ v₂ : Var Γ A)
  (neq : ¬ v₁ = v₂) : (γ.set v₂ val).get v₁ = γ.get v₁
  := by
  induction Γ with
  | nil => cases v₁
  | cons B Γ Γ_ih =>
    cases v₁ with
    | vz =>
      cases v₂ with
      | vz => aesop
      | vs v₂ => simp_all only [reduceCtorEq, not_false_eq_true]; rfl
    | vs v₁ =>
      cases v₂ with
      | vz => aesop
      | vs v₂ =>
        simp_all only [Var.vs.injEq]
        apply Γ_ih
        simp_all only [not_false_eq_true]

/-- We can ignore a `set` if we're setting a different variable from the one we're reading. -/
@[aesop unsafe 10%] theorem ConA.get_set_irrelevant_heq {Γ : Con} {γ : Γ} {v₁ : Var Γ A} {v₂ : Var Γ B}
  (neq : ¬ HEq v₁ v₂) : (γ.set v₂ val).get v₁ = γ.get v₁
  := by
  induction Γ with
  | nil => cases v₁
  | cons C Γ Γ_ih =>
    cases v₁ with
    | vz =>
      cases v₂ with
      | vz => simp_all only [heq_eq_eq, not_true_eq_false]
      | vs v₂ => rfl
    | vs v₁ =>
      cases v₂ with
      | vz => rfl
      | vs v₂ =>
        apply Γ_ih
        have : ¬(@HEq (Var (C :: Γ) A) v₁.vs (Var (C :: Γ) B) v₂.vs) -> ¬HEq v₁ v₂ := by
          -- Var.vs.injEq but HEq...
          sorry
        exact this neq


/-- We can ignore a `set` if we're setting a different variable from the one we're reading.
  This is necessarily the case when the variables have a different type. -/
@[aesop unsafe 8%] theorem ConA.get_irrelevant_set_Ty {Γ : Con} {γ : Γ} {v₁ : Var Γ A} {v₂ : Var Γ B}
  (neq : ¬ A = B) : (γ.set v₂ a').get v₁ = γ.get v₁
  := by
    -- have v_neq : ¬HEq v v' := Var.neq_neq_Ty neq
    induction Γ with
    | nil => simp_all only
    | cons C Γ ih =>

      sorry

theorem ConA.ext {Γ : Con} (A : Ty) {γ γ' : Γ} (h : ∀{A}, ∀v : Var Γ A, γ.get v = γ'.get v) : γ = γ' := by
  induction Γ with
  | nil => rfl
  | cons A Γ Γ_ih =>
    let ⟨a, γ⟩ := γ
    let ⟨a', γ'⟩ := γ'
    sorry
