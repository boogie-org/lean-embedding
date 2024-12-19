import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import LeanBoogie.Util

namespace LeanBoogie

/- # Codes for Boogie types

-/

/-- Codes for Boogie types.

  An alternative formulation would be forgo `Ty` entirely and define `def Con : Type 1 := List Type`,
  which would allow for arbitrary types.
-/
@[aesop unsafe cases 1%]
inductive Ty /- (Ptr : Type) -/ : Type
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

-- /-- Pointers are just variables. This implies pointers always point into valid memory, and
--   always point to something that actually has type `A`.
--   This is (in my opinion --Max), the theoretically ideal way of modeling pointers. However, it comes
--   with a big issue: It requires induction-induction (ind-ind), which Lean doesn't natively support.
--   This is because we need to wrap `Con : Type`, `Ty : Type`, and `Var : Con -> Ty -> Type` into one
--   mutual block, and `Var` is a type constructor which refers to the other types in the same
--   mutual block; this is ind-ind.
--   Fortunately, ind-ind can be reduced to Lean's mutual inductive types, and there exists a repo
--   which does that, although it is a bit out of date: https://github.com/javra/iit .
--   A fork updating it to Lean 4.6 is at https://github.com/arthur-adjedj/iit/tree/bump/4.6.0 .
--   While that repo automates the process, it is a little buggy and unmaintained. It is not too
--   difficult to do this reduction by hand: You split your ind-ind type up into an erased half with
--   no type indices at all, and a wellformedness half (in Prop) which add indices back. Then you
--   subtype those together. -/
-- | var {A : Ty} {Γ : Con} (v : Var Γ A) : Ty

-- /-- A pointer into some `Ty.map A B`, i.e. storing the key of the map.
--   This requires induction-recursion (ind-rec), because we have to define the recursive function
--   `TyA : Ty -> Type` in the same mutual block as `Ty`.
--   You can work around this, either by using a similar approach to reducing induction-induction,
--   or by using the approach described in https://akaposi.github.io/pres_types_2023.prf slide 6.
--   Intuitively, Kaposi's approach would store the result of the recursive function `TyA A` as a
--   type index on every constructor of `Ty`.  -/
-- | ptr {A B : Ty} : TyA A -> Ty

-- /-- Pointer into some `Ty.map Ptr B`, for example `Ty.map (BitVec 32) B`. This requires no
--   ind-ind or ind-rec, but only allows for one pointer type. You also can not refer to other
--   variables in the context. There is no way of knowing which mapping you refer to, if your
--   context stores more than one `Ty.map`. -/
-- | ptr {B : Ty} : Ptr -> Ty
deriving Repr, DecidableEq
infixl:20 " ~> " => Ty.map

abbrev Ty.bv64 : Ty := .bv 64
abbrev Ty.bv32 : Ty := .bv 32
abbrev Ty.bv16 : Ty := .bv 16
abbrev Ty.bv8 : Ty := .bv 8
abbrev Ty.bv1 : Ty := .bv 1

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

def Con.getByVar : (Γ : Con) -> Var Γ A -> Ty
| .(A) :: _, .vz => A
| _ :: Γ, .vs v => Con.getByVar Γ v

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

theorem ConA.ext {Γ : Con} (A : Ty) {γ γ' : Γ} (h : ∀{A}, ∀v : Var Γ A, γ.get v = γ'.get v) : γ = γ' := by
  induction Γ with
  | nil => rfl
  | cons A Γ Γ_ih =>
    let ⟨a, γ⟩ := γ
    let ⟨a', γ'⟩ := γ'
    sorry

/-- `Γ - n = (Γ[n] :: (Γ - (n+1)))`.
  For example `[A, B, C].drop 0 = (A :: [A, B, C].drop 1)`, since `[A, B, C].drop 1 = [B, C]`. -/
theorem Con.drop_n_1 {Γ : Con} {hn : n < List.length Γ} {hn_11 : n + 1 < List.length Γ + 1} {hn_1}
  : Γ.drop ⟨n, hn_1⟩ = Γ.get ⟨n, hn⟩ :: Γ.drop ⟨n+1, hn_11⟩
  := by
    induction n with
    | zero =>
      induction Γ with
      | nil => exact (Nat.not_lt_zero 0 hn).elim
      | cons A Γ ih_Γ => rfl
    | succ n ih_n =>
      induction Γ with
      | nil => rw [List.length] at hn_1; simp only [zero_add, add_lt_iff_neg_right, not_lt_zero'] at hn_1
      | cons A Γ ih_Γ =>
        sorry

theorem Con.drop_n_1_A {Γ : Con} {hn : n < Γ.length} {hn_1} {hn_11 : n + 1 < Γ.length + 1}
  : ConA (Γ.drop ⟨n, hn_1⟩) = (TyA (Γ.get ⟨n, hn⟩) × ConA (Γ.drop ⟨n + 1, hn_11⟩))
  := by rw [Con.drop_n_1]

/-- `γ - n = (γ[n], γ - (n+1))`.
  For example `(a, b, c, ()).drop 0 = (a, (a, b, c).drop 1)`. -/
theorem ConA.drop_n_1 {Γ : Con} {A : Ty} {γ : Γ} {hn_1} {hn : n < List.length Γ} {hn_11 : n + 1 < List.length Γ + 1}
  : ConA.drop γ ⟨n, hn_1⟩ = Con.drop_n_1_A.symm ▸ (ConA.get γ (Var.ofIdx ⟨n, hn⟩), ConA.drop γ ⟨n+1, hn_11⟩)
  := by sorry

/- ## Normal form of `ConA`
  Given a state `γ : ConA Γ`, we can normalize it into a `Prod.mk` telescope that is equal to
  `(γ.get v0, γ.get v1, γ.get v2, ...)`.
  This is done automatically using the `normalize` tactic.

  Alternative approaches:
  - Use `DiscrTree` or `LazyDiscrTree` for matching against a large amount of patterns.
    `simp` uses those internally and is quite efficient.
  - Use simprocs instead of the following normalize tactic.

  We should eventually have a delaborator which can render states `γ : ConA Γ` in a more
  human-readable way.
-/

namespace Example
private def Γ : Con := [.int, .int]
private def Stuff : Type := ConA Γ
private def Stuff.mk (i : Int) (x : Int) : Stuff := (i, x, ())
private def Stuff.i (self : Stuff) : Int := ConA.get self .v0
private def Stuff.x (self : Stuff) : Int := ConA.get self .v1
private example : (Stuff.mk i x).i = i := rfl
private example : (Stuff.mk i x).x = x := rfl
private def Stuff.normalize (s : Stuff) : s = Stuff.mk s.i s.x := by rfl
end Example

open Lean Elab Tactic Meta Qq

def Ty.toExpr : Ty -> Q(Ty)
| .int => q(.int)
| .real => q(.real)
| .bool => q(.bool)
| .bv n => q(.bv $n)
| .map A B =>
  let Ae := toExpr A
  let Be := toExpr B
  q(.map $Ae $Be)

instance : ToExpr Ty where
  toExpr := Ty.toExpr
  toTypeExpr := q(Ty)

def Con.toExpr : Con -> Q(Con)
| [] => q([])
| A :: Γ =>
  let Γe := toExpr Γ
  q($A :: $Γe)

instance : ToExpr Con where
  toExpr := Con.toExpr
  toTypeExpr := q(Con)

def Var.toExpr {Γ : Con} {A : Ty} : Var Γ A -> Q(Var $Γ $A)
| .vz => q(Var.vz)
| .vs v =>
  let vExpr := toExpr v
  q(Var.vs $vExpr)

instance : ToExpr (Var Γ A) where
  toExpr := Var.toExpr
  toTypeExpr := q(Var $Γ $A)

set_option linter.unusedVariables false in
def Con.casesQ {motive : Type} (Γ : Q(Con))
  (nil : {p : $Γ =Q []} -> MetaM motive)
  (cons : (A : Q(Ty)) -> (Γ' : Q(Con)) -> ($Γ =Q $A :: $Γ') -> MetaM motive)
  : MetaM motive
  := do
  if let .defEq p := (<- isDefEqQ Γ q(@List.nil Ty)) then
    return <- nil (p := p)
  else
    let Γ' <- mkFreshExprMVarQ q(Con)
    let A <- mkFreshExprMVarQ q(Ty)
    let .defEq p := <- isDefEqQ Γ q($A :: $Γ')
      | throwError "ConQ.cases: Non-exhaustive match on {repr Γ}"
    return <- cons A Γ' p

/-- Map every variable for context `Γ` using `f`. -/
partial def ConQ.mapM (Γ : Q(Con)) {B : Type} (f : {A : Q(Ty)} -> Q(Var $Γ $A) -> MetaM B) : MetaM (List B) := do
  Con.casesQ Γ (return []) fun A Γ' _ => do
    let b : B <- f (A := A) q(@Var.vz $A $Γ') -- `Γ` =?= `A :: Γ'`
    let f' : {A : Q(Ty)} -> Q(Var $Γ' $A) -> MetaM B := fun v => f q(Var.vs $v)
    return b :: (<- ConQ.mapM Γ' f')

structure GetIrrelevantResult (A : Q(Ty)) (orig : Q(TyA $A)) where
  eNew : Q(TyA $A)
  prfEq : Q($orig = $eNew)

instance : Inhabited (GetIrrelevantResult A orig) := ⟨{ eNew := orig, prfEq := q(Eq.refl $orig) }⟩


#check DiscrTree
#check LazyDiscrTree

-- Γ - n = (Γ[n] :: Γ - (n+1))
-- γ - n = (γ.get n, γ - (n+1))

/-- Gets a value from a state, stripping away irrelevant setters/getters.

  Input is an expression `γ {|>.set .. |>.get ..}* : ConA Γ`, so a state `γ : ConA Γ`,
  usually followed by a mix of setters and getters.
  Output is `e' : TyA A`, where `e'` is made up of only `γ.get`, such that `γ.get v = e'`.

  Examples (one per line, pseudocode, with `x ≠ y`):
  ```
  getQ _ q(γ |>.set x 10 |>.set y 20) _ x = q(10)
  getQ _ q(γ |>.set x 10 |>.set y 20) _ y = q(20)
  getQ _ q(γ |>.set y 20) _ x = q(γ.get x)
  ```

  _Implementation notes:_
  This function is implemented very inefficiently, using plenty of metavariables and `isDefEq` (i.e.
  unification) to match against patterns. Unification will expand definitions, do beta-reduction,
  iota-reduction (i.e. look "through" eliminators for inductive types), and many other things,
  which is probably overkill for our use case.
  A more efficient implementation would use `whnf` and `myexpr.isAppOf` and
  match each argument manually. However, I have decided against this for now, because getting that
  right is very fiddly and error-prone, and very hard to wrap your head around for anyone new to Lean.
  Also, `match_expr` and `let_expr` could be useful.
-/
partial def ConA.getQ (Γ : Q(Con)) (γ : Q(ConA $Γ)) (A : Q(Ty)) (v : Q(Var $Γ $A)) : MetaM (GetIrrelevantResult A q(ConA.get $γ $v)):= do
  let mut cur : GetIrrelevantResult A q(ConA.get $γ $v) := default
  while true do
    if let .some ⟨eNew, (prfEq : Q($(cur.1) = $eNew))⟩ := <- go cur.1 then
      cur := {
        eNew := eNew,
        prfEq := q(Eq.trans $cur.prfEq $prfEq)
      }
    else break
  return cur
where go (e : Q(TyA $A)) : MetaM (Option <| GetIrrelevantResult A e) := do
  let γ <- mkFreshExprMVarQ q(ConA $Γ)
  let B <- mkFreshExprMVarQ q(Ty)
  let v₁ <- mkFreshExprMVarQ q(Var $Γ $A)
  let v₂ <- mkFreshExprMVarQ q(Var $Γ $B)
  let val <- mkFreshExprMVarQ q(TyA $B)
  if <- isDefEq e q($γ |>.set $v₂ $val |>.get $v₁) then -- match `e =?= (some pattern)`. Inefficient, but (relatively) painless.
    if <- isDefEq A B then -- this isDefEq is a bit too strong: we might have `v₁ = v₂` but not quite `v₁ ≡ v₂`.
      let v₂ : Q(Var $Γ $A) := v₂ -- well-typed because A≡B
      let val : Q(TyA $A) := val -- well-typed because A≡B
      return <- ifQ q($v₁ = $v₂)
        (@fun prf => do
          -- * Case `γ |>.set v₂ val |>.get v₁` where `v₁ = v₂` results in `val`. We're done!
          return some {
            eNew := val,
            prfEq := mkApp q(@ConA.get_set' $A $val $Γ $v₁ $v₂ $γ) prf
          }
        )
        (@fun prf => do
          -- * This setter is irrelevant because it sets a different variable than the one we're reading.
          return some {
            eNew := q($γ |>.get $v₁)
            prfEq := mkApp q(ConA.get_set_irrelevant (γ := $γ) (val := $val) $v₁ $v₂) prf
          }
        )
    else -- `A` not defeq `B`
      return <- ifQ q($A = $B)
        (do
          logWarning m!"ConAQ.get_irrelevant: Have `A = B` but not `A ≡ B`, but not using this knowledge. At `e` = {e}"
          return none
        )
        (@fun prf =>
          -- * This setter is irrelevant because it sets a different variable than the one we're reading.
          return some {
            eNew := q($γ |>.get $v₁)
            prfEq := mkApp q(@ConA.get_irrelevant_set_Ty $A $B $val $Γ $γ $v₁ $v₂) prf
          }
        )
  return none

structure NormalizeResult' (Γ : Q(Con)) (γ₀ : Q(ConA $Γ)) (n : Nat) where
  hn : Q($n < ($Γ).length + 1)
  γ_n' : Q(ConA (Con.drop $Γ ⟨$n, $hn⟩)) -- for n=0, this is `ConA Γ`
  prfEq : Q(ConA.drop $γ₀ ⟨$n, $hn⟩ = $γ_n') -- for n=0, this is `γ₀ = γ_n'`

structure NormalizeResult (Γ : Q(Con)) (γ : Q(ConA $Γ)) where
  γ' : Q(ConA $Γ)
  prfEq : Q($γ = $γ')

theorem Nat.ne_nlt_therefore_lt {n m : Nat} (h₁: ¬ n > m) (h₂ : ¬ n = m) : n < m :=
  match Nat.lt_or_lt_of_ne h₂ with
  | .inl h => h
  | .inr h => False.elim (h₁ h)

partial def ConA.normalize.go (Γ : Q(Con)) (γ : Q(ConA $Γ)) (n : Nat) (hn : Q($n < ($Γ).length + 1)) : MetaM (NormalizeResult' Γ γ n) := do
  let Γ_len : Q(Nat) := q(List.length $Γ)
  ifQ q($n > $Γ_len)
    (do
      throwError "ConAQ.normalize: Our n (={n}) is bigger than Γ.length (={Γ_len})!, Γ={Γ}"
    )
    (@fun h₁ => do
      ifQ q($n = $Γ_len)
        (do
          -- `Γ - Γ.length = []`, thus `γ - Γ.length = ()`. We are done.
          return {
            hn := hn
            γ_n' := (q(()) : Expr)
            prfEq := (q(@Eq.refl.{1} Unit ()) : Expr)
          }
        )
        (@fun h₂ => do
          have h₃ : Q($n < $Γ_len) := q(Nat.ne_nlt_therefore_lt $h₁ $h₂)
          let A <- mkFreshExprMVarQ q(Ty)
          let Γ_n1 <- mkFreshExprMVarQ q(Con)
          let ⟨_prf⟩ <- assertDefEqQ q(List.cons $A $Γ_n1) q(Con.drop $Γ $n) -- okay because `(drop Γ n).length > 0` because h₃
          -- We know that `drop Γ n = A :: Γ_n1`
          let ⟨h_n1, γ_n1', γ_n1_eq_γ_n1'⟩ <- normalize.go Γ γ (n+1) q(Nat.add_lt_add_right $h₃ 1)
          let v_n : Q(Var $Γ (($Γ).get ⟨$n, $h₃⟩)) := q(Var.ofIdx ⟨$n, $h₃⟩)

          -- assertDefEq "Γ[n] ≡ A" q(($Γ).get ⟨$n, $h₃⟩) A -- this just so happens to hold often
          let ⟨val_irrelevant, val_irrelevant_eq⟩ <- ConA.getQ Γ γ q(($Γ).get ⟨$n, $h₃⟩) v_n
          return {
            hn := hn
            -- γ_n' := q(Con.drop_n_1_A.symm ▸ Prod.mk (ConA.get (A := ($Γ).get ⟨$n, $h₃⟩) $γ $v_n) $γ_n1') -- this is probably defeq in every context we use...
            -- prfEq := q($γ_n1_eq_γ_n1' ▸ @ConA.drop_n_1 _ _ (($Γ).get ⟨$n, $h₃⟩) $γ $hn $h₃ $h_n1)
            γ_n' := q(Con.drop_n_1_A.symm ▸ Prod.mk $val_irrelevant $γ_n1') -- this is probably defeq in every context we use...
            prfEq := q($val_irrelevant_eq ▸ $γ_n1_eq_γ_n1' ▸ @ConA.drop_n_1 _ _ (($Γ).get ⟨$n, $h₃⟩) $γ $hn $h₃ $h_n1)
          }
        )
    )

-- look into omega (or linarith)

/-- Normalize a state `γ : ConA Γ` into form `(γ.get v0, (γ.get v1, (γ.get v2, ...)))`. -/
def ConA.normalize (Γ : Q(Con)) (γ : Q(ConA $Γ)) : MetaM (NormalizeResult Γ γ) := do
  let ⟨_, γ_0', rw⟩ <- normalize.go Γ γ 0 q(Nat.zero_lt_succ (List.length $Γ))
  return {
    γ' := q(/- @Con.drop_0 $Γ (Nat.zero_lt_succ (List.length $Γ)) ▸ -/ $γ_0') -- the cast is not necessary because it holds definitionally
    prfEq := rw
  }

theorem eq_congr (ha : lhs = lhs') (hb : rhs = rhs') : (lhs' = rhs') -> (lhs = rhs)
  := by cases ha; cases hb; exact id

elab "normalize" : tactic => do
  let φ_proof <- getMainGoal
  φ_proof.withContext do
    let Γ : Q(Con) <- mkFreshExprMVar q(Con) .natural `Γ
    let lhs <- mkFreshExprMVarQ q(ConA $Γ) .natural `lhs
    let rhs <- mkFreshExprMVarQ q(ConA $Γ) .natural `rhs
    let φ : Q(Prop) <- getMainTarget
    let .true <- isDefEq φ q(@Eq (ConA $Γ) $lhs $rhs) | throwError "Expected an equality on `ConA _`"
    let Γ : Q(Con) <- instantiateMVarsQ Γ (u := 1)

    let lhs_norm <- ConA.normalize Γ lhs
    let rhs_norm <- ConA.normalize Γ rhs
    let lhs' := lhs_norm.γ'
    let rhs' := rhs_norm.γ'
    let lhs'_prf := lhs_norm.prfEq
    let rhs'_prf := rhs_norm.prfEq
    -- assertDefEq "lhs = lhs'" (<- inferType lhs'_prf) (mkApp2 q(@Eq (ConA $Γ)) lhs lhs') -- just for debugging
    -- assertDefEq "rhs = rhs'" (<- inferType rhs'_prf) (mkApp2 q(@Eq (ConA $Γ)) rhs rhs') -- just for debugging
    -- logInfo m!"lhs'_prf : {<- inferType lhs'_prf}"
    let φ'_proof <- mkFreshExprMVarQ q(@Eq (ConA $Γ) $lhs' $rhs') .natural
    let prf := mkAppN q(@eq_congr (ConA $Γ)) #[lhs, lhs', rhs, rhs', lhs'_prf, rhs'_prf]
    -- logInfo m!"prf ≣ {prf}"
    φ_proof.assign (.app prf φ'_proof)
    replaceMainGoal [φ'_proof.mvarId!]
