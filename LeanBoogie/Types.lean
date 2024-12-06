import Mathlib.Data.Real.Basic

namespace LeanBoogie

-- # Codes for boogie state types

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
/-- Real numbers. Interpreted as `ℝ`.

  Reals are not computable!
-/
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

abbrev Ty.bv64 : Ty := .bv 64
abbrev Ty.bv32 : Ty := .bv 32
abbrev Ty.bv16 : Ty := .bv 16
abbrev Ty.bv8 : Ty := .bv 8
abbrev Ty.bv1 : Ty := .bv 1

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

abbrev Var.v0 : Var (A :: Γ) A := .vz
abbrev Var.v1 : Var (B :: A :: Γ) A := .vs .vz
abbrev Var.v2 : Var (C :: B :: A :: Γ) A := .vs (.vs .vz)
abbrev Var.v3 : Var (D :: C :: B :: A :: Γ) A := .vs (.vs (.vs .vz))

/-- Interprets e.g. `Ty.int` into `Int`. -/
abbrev TyA : Ty -> Type
| .int => Int
| .real => Real
| .bool => Bool
| .bv bits => BitVec bits
| .map A B => TyA A -> TyA B

-- So that you can do e.g. `(my_int : .int) -> ...` instead of `(my_int : TyA .int) -> ...`.
instance : CoeSort Ty Type := ⟨TyA⟩

def TyA.inhabited : {A : Ty} -> A
| .int => default
| .real => default
| .bool => default
| .bv _ => default
| .map _ _ => fun _ => inhabited

instance : Inhabited (TyA A) := ⟨TyA.inhabited⟩

-- instance : Equiv Ty.bv1 Ty.bool where


/-- E.g. `ConA [.int, .bv 32] ≣ Unit × Int × BitVec 32`. -/
abbrev ConA : Con -> Type
| [] => Unit
| x :: xs => TyA x × ConA xs

instance : CoeSort Con Type := ⟨ConA⟩
def ConA.inhabited : {Γ : Con} -> Γ
| [] => ()
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


@[aesop safe] theorem Var.emptyΓ_False (v : Var [] A) : False := by cases v
@[aesop safe] theorem Var.neq_neq_Ty {v : Var Γ A} {v' : Var Γ B} (h : A ≠ B) : ¬HEq v v' := by
  intro h'
  induction Γ with
  | nil => exact Var.emptyΓ_False v
  | cons C Γ ih => sorry -- cases v, cases v'

@[aesop safe] theorem ConA.get_irrelevant_set_Var {Γ : Con} {γ : Γ} (v v' : Var Γ A)
  (neq : ¬ v = v') : (γ.set v' a').get v = γ.get v
  := by
  induction Γ with
  | nil => cases v
  | cons B Γ Γ_ih => sorry -- cases v; cases v'; ...

/-- We can ignore a `set` if we're setting a different variable from the one we're reading.
  This is necessarily the case when the variables have a different type. -/
@[aesop safe] theorem ConA.get_irrelevant_set_Ty {Γ : Con} {γ : Γ} {v : Var Γ A} {v' : Var Γ B}
  (neq : ¬ A = B) : (γ.set v' a').get v = γ.get v
  := by have neq : ¬HEq v v' := Var.neq_neq_Ty neq; sorry

/-- When you have `γ : Γ`, you can rewrite it as the following, for arbitrary `γ'` (e.g. `default`).
  ```
  γ'
    |>.set v0 (γ.get v0)
    |>.set v1 (γ.get v1)
    |>.set v2 (γ.get v2)
    ... -- continue for all variables in Γ
  ```
  Using this, we can normalize
-/
def spread : (Γ : Con) -> Γ -> Γ
| [], () => ()
| _ :: Γ, (a, γ) => ConA.set (a, spread Γ γ) .vz (ConA.get (a, γ) .vz)

theorem spread_id (Γ : Con) : spread Γ = id := by
  induction Γ with
  | nil => rfl
  | cons Γ A ih => simp [spread, ih]; rfl

-- example {Γ : Con} (γ : Γ) (v : Var Γ A) : γ =

/-- "Grab" one variable from the state. This gives you something that contains a projection `.get v`
  applied to your original state `γ`, so that you can use `get_irrelevant_set_Var` and
  `get_irrelevant_set_Ty` to only get the `.set v` that matters.

  Then by repeating `ConA.grab` for every variable, you can normalize your `ConA Γ` into exactly
  one `.set` for every variable.
-/
theorem ConA.grab {Γ : Con} {γ : Γ} (v : Var Γ A) : γ = γ.set v (γ.get v) := by
  induction Γ with
  | nil => rfl
  | cons B Γ ih_Γ =>
    cases v with
    | vz => rfl
    | vs v =>
      obtain ⟨fst, snd⟩ := γ
      ext : 1
      · simp_all only
        rfl
      · simp_all only
        apply ih_Γ

/-
  ## Pseudo-structures
-/

def Γ : Con := [.int, .int]
def Stuff : Type := ConA Γ
def Stuff.mk (i : Int) (x : Int) : Stuff := (i, x, ())
def Stuff.i (self : Stuff) : Int := ConA.get self .v0
def Stuff.x (self : Stuff) : Int := ConA.get self .v1
example : (Stuff.mk i x).i = i := rfl
example : (Stuff.mk i x).x = x := rfl
