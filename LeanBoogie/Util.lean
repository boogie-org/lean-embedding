import Lean
import Qq

open Lean Elab Meta Term Qq in
elab "reduceType! " t:term : term => do
  let t <- elabTerm t none
  let tType <- inferType t
  withTransparency TransparencyMode.default do
    let tTypeReduced <- reduceAll tType
    let t' := Expr.letE `t tTypeReduced t (.bvar 0) false
    return t'

open Lean Qq

-- #check instantiateExprMVarsQ

-- Some utils for Quote4
def instantiateExprMVarsQ {m : Type → Type} {A : Q(Type)} [Monad m] [MonadMCtx m] [STWorld ω m] [MonadLiftT (ST ω) m] (e : Q($A)) : m Q($A) := do
  let this <- instantiateMVars e
  return this

def withRefQ {m : Type → Type} {A : Q(Type)} [Monad m] [MonadRef m] (ref : Syntax) (x : m Q($A)) : m Q($A) := Lean.withRef ref x
