import LeanBoogie.ConTy

namespace LeanBoogie


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

open Lean Elab Tactic Meta Qq

def Ty.toExpr : Ty -> Q(Ty)
| .unit => q(.unit)
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


structure GetIrrelevantResult (A : Q(Ty)) (orig : Q(TyA $A)) where
  eNew : Q(TyA $A)
  prfEq : Q($orig = $eNew)

instance : Inhabited (GetIrrelevantResult A orig) := ⟨{ eNew := orig, prfEq := q(Eq.refl $orig) }⟩

/-- Given an expressino `x.get v`, removes all irrelevant setters from `x`.
  Example: `γ |>.set v₁ _ |>.get v₂` becomes `γ |>.get v₂` when `v₁ ≠ v₂`. -/
def TyA.stripIrrelevant (Γ : Q(Con)) {A : Q(Ty)} (e : Q(TyA $A)) : MetaM (Option <| GetIrrelevantResult A e) := do
  let γ <- mkFreshExprMVarQ q(ConA $Γ)
  let B <- mkFreshExprMVarQ q(Ty)
  let v₁ <- mkFreshExprMVarQ q(Var $Γ $A)
  let v₂ <- mkFreshExprMVarQ q(Var $Γ $B)
  let val <- mkFreshExprMVarQ q(TyA $B)
  if <- isDefEq e q($γ |>.set $v₂ $val |>.get $v₁) then -- match `e =?= (some pattern)`. Inefficient, but (relatively) painless.
    if <- isDefEq A B then -- this isDefEq is a bit too strong: we might have `A = B` but not quite `A ≡ B`.
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

simproc normTyA (ConA.get (ConA.set _ _ _) _) := fun e => do
  let Γ : Q(Con) <- mkFreshExprMVarQ q(Con)
  let A : Q(Ty) <- mkFreshExprMVarQ q(Ty)
  if let some { eNew, prfEq } := <- TyA.stripIrrelevant (A := A) Γ e then
    let step : Simp.Step := Simp.Step.continue <| some {
      expr := eNew
      proof? := prfEq
    }
    return step
  else
    return .done { expr := e }



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
    if let .some ⟨eNew, (prfEq : Q($(cur.1) = $eNew))⟩ := <- TyA.stripIrrelevant Γ cur.1 then
      cur := {
        eNew := eNew,
        prfEq := q(Eq.trans $cur.prfEq $prfEq)
      }
    else break
  return cur

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

/-- Recursively (with `n` *increasing*!) go through the `Prod.mk`-telescope `γ` and apply `.get`. -/
partial def ConA.normalize.go (Γ : Q(Con)) (γ : Q(ConA $Γ)) (n : Nat) (hn : Q($n < ($Γ).length + 1)) : MetaM (NormalizeResult' Γ γ n) := do
  withTraceNode `LeanBoogie.normConTy (logger' m!"ConA.normalize.go {γ} VAR#{n}") do
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

/-- Normalize a state `γ : ConA Γ` into form `(γ.get v0, (γ.get v1, (γ.get v2, ...)))`.
  This is a very inefficient implementation in two regards:
  1. It is not optimized.
  2. More importantly, for every variable it builds `γ.get v` and normalizes that. Often, the state
     changes only in some variables, so if `γ = (a, b, c, ()).set "a" 123`, then we first build
     `γ' = (γ.get "a", γ.get "b", γ.get "c", ())` which is a bit unnecessary.
     The advantage is that it's "relatively" easy to build automation for.
-/
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
