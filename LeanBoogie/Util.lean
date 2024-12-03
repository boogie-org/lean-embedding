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

-- Some utils for Quote4
def instantiateExprMVarsQ {m : Type → Type} {A : Q(Type)} [Monad m] [MonadMCtx m] [STWorld ω m] [MonadLiftT (ST ω) m] (e : Q($A)) : m Q($A) := do
  let this <- instantiateMVars e
  return this

def withRefQ {m : Type → Type} {A : Q(Type)} [Monad m] [MonadRef m] (ref : Syntax) (x : m Q($A)) : m Q($A) := Lean.withRef ref x

/-- A version of `Array.findIdx?` but also returns a proof that the index is valid. -/
def Array.findIdxH? (as : Array A) (h : as.size <= N) (p : A -> Bool) : Option (Fin N) :=
  let rec loop (j : Nat) : Option (Fin N) :=
    if h' : j < as.size then
      if p as[j] then some ⟨j, by omega⟩ else loop (j + 1)
    else none
  loop 0

/-- A version of `List.findIdx?` but also returns a proof that the index is valid. -/
def List.findIdxH? (as : List A) (h : as.length <= N) (p : A -> Bool) : Option (Fin N) :=
  let rec loop (j : Nat) : Option (Fin N) :=
    if h' : j < as.length then
      if p as[j] then some ⟨j, by omega⟩ else loop (j + 1)
    else none
  loop 0

def List.q {A : Q(Type)} : List Q($A) -> Q(List $A)
| [] => q([])
| x :: xs => let xs := q xs; q($x :: $xs)

def List.q_len {A : Q(Type 1)} : (N:Nat) -> (xs : List Q($A)) -> xs.length = N -> Q((xs : List $A) ×' xs.length = $N)
| 0, [], h => by cases h; exact q(⟨[], rfl⟩)
| N+1, x :: xs, h => by
  let xs := q_len N xs (by rw [List.length] at h; omega)
  exact q(⟨$x :: ($xs).fst, by rw [List.length]; rw [($xs).snd]⟩)

-- For illustrative purposes, we want to suppress "warning: declaration uses sorry" often.
axiom sorry! {P} : P
macro "sorry!" : tactic => `(tactic| exact sorry!)
