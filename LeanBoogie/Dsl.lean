import Lean
import Std
import Qq
import LeanBoogie.ITree
import LeanBoogie.Effect.Mem
import LeanBoogie.Effect.AssumeAssert
import LeanBoogie.State
import LeanBoogie.TraceClasses
import Batteries.Data.Array.Monadic

namespace LeanBoogie
open Lean Elab Term Meta Qq
open Std (HashSet HashMap)

open ITree

/-
  # Boogie DSL
  There's an official Lean guide here: https://leanprover-community.github.io/lean4-metaprogramming-book/main/08_dsls.html
-/

-- ## Syntax

section Syntax
  syntax BoogieIdent := ("$" noWs)? ident

  declare_syntax_cat BoogieType
  syntax "unit" : BoogieType
  syntax "int" : BoogieType
  syntax "bool" : BoogieType
  -- syntax "bv" noWs num : BoogieType -- Can we get something like this to work?
  syntax "bv32" : BoogieType
  syntax "bv16" : BoogieType
  syntax "bv8" : BoogieType
  syntax "bv4" : BoogieType
  syntax "bv2" : BoogieType
  syntax "bv1" : BoogieType

  declare_syntax_cat BoogieVarBinder
  syntax ident ": " BoogieType : BoogieVarBinder

  declare_syntax_cat BoogieExpr
  syntax:60 " -" BoogieExpr : BoogieExpr
  syntax:50 BoogieExpr " * " BoogieExpr : BoogieExpr
  syntax:50 BoogieExpr " / " BoogieExpr : BoogieExpr
  syntax:40 BoogieExpr " + " BoogieExpr : BoogieExpr
  syntax:40 BoogieExpr " - " BoogieExpr : BoogieExpr
  syntax:30 BoogieExpr " <= " BoogieExpr : BoogieExpr
  syntax:30 BoogieExpr " == " BoogieExpr : BoogieExpr
  syntax ident noWs "(" BoogieExpr,* ")" : BoogieExpr -- boogie pure function call (non-effectful)
  syntax ident : BoogieExpr -- variable
  syntax num (noWs "bv" noWs num)? : BoogieExpr -- BitVec literal, e.g. `10bv32`
  -- syntax num (noWs "bv" noWs num)? : term -- BitVec literal, e.g. `10bv32`
  -- #check 123bv1
  syntax "(" BoogieExpr ")" : BoogieExpr

  /-- Formulas can do things that boogie (boolean) expressions can't, e.g. forall quantifiers. -/
  declare_syntax_cat BoogieFormula
  syntax ident : BoogieFormula -- variables
  syntax:60 "(" BoogieFormula ")" : BoogieFormula
  syntax:60 " !" BoogieFormula : BoogieFormula
  syntax BoogieExpr:100 " == " BoogieExpr:100 : BoogieFormula
  syntax BoogieExpr:100 " <= " BoogieExpr:100 : BoogieFormula
  syntax BoogieExpr:100 " < "  BoogieExpr:100 : BoogieFormula
  syntax:50 BoogieFormula " && " BoogieFormula : BoogieFormula
  syntax:40 BoogieFormula " || " BoogieFormula : BoogieFormula
  syntax:30 BoogieFormula " => " BoogieFormula : BoogieFormula
  syntax:20 "∀" ident ": " BoogieType ", " BoogieFormula : BoogieFormula

  declare_syntax_cat BoogieAssume
  syntax "assume " BoogieFormula "; " : BoogieAssume
  declare_syntax_cat BoogieGoto
  syntax "goto " ident,* "; " : BoogieGoto -- once `return`s work, change this `*` into a `+`
  declare_syntax_cat BoogieReturn
  syntax "return" "; " : BoogieReturn

  declare_syntax_cat BoogieCommand
  syntax ident " := " BoogieExpr "; " : BoogieCommand
  syntax "if " BoogieExpr " { " BoogieCommand* " }" ("else" " { " BoogieCommand* " }")? : BoogieCommand
  syntax "while " BoogieExpr " { " BoogieCommand* " }" : BoogieCommand
  syntax "call " BoogieIdent "(" BoogieExpr,* ")" "; " : BoogieCommand
  syntax BoogieAssume : BoogieCommand


  declare_syntax_cat BoogieBlock
  syntax BoogieBlockGotoOrReturn := BoogieGoto <|> BoogieReturn
  syntax ident ": " BoogieAssume* BoogieCommand* BoogieBlockGotoOrReturn : BoogieBlock

  declare_syntax_cat BoogieVarCmd
  syntax "var " BoogieVarBinder "; " : BoogieVarCmd

  -- syntax BoogieBlocksOrCommands := (BoogieBlock* <|> BoogieCommand*) -- this should fail fast, because blocks uniquely need to start with a label.
  declare_syntax_cat BoogieProc
  syntax "procedure " ident "(" BoogieVarBinder,* ")"
    (" returns " "(" BoogieVarBinder ")")?
    " { "
      BoogieVarCmd*
      BoogieCommand* -- these "blockless" commands will get wrapped into a block of their own, if there are any subsequent blocks
      (BoogieBlockGotoOrReturn)?
      BoogieBlock*
    " }" : BoogieProc

  -- syntax ident,+ " := " BoogieExpr,+ ";" : BoogieCommand
  -- macro_rules
  -- | `(BoogieCommand| $x:ident , $xs:ident,* := $e:BoogieExpr , $es:BoogieExpr,*; ) => do
  --   `(BoogieCommand| $x:ident := $e:BoogieExpr; $xs := $es; )
end Syntax







/-
  ## Elaboration
  Takes `Lean.Syntax` (or, well, `Lean.TSyntax`) and spits out `Lean.Expr`.
-/

section Elab

/-- Our choice of effects for Boogie programs: `Mem Γ` and `AmAt` (assume and assert).

Eventually, we should be generic over the effects, using machinery such as `HasEffect` etc. -/
abbrev EffB (Γ : Con) := Mem Γ
-- abbrev EffB (Γ : Con) := Mem Γ & AmAt

/-- An elaborated boogie block.

  Ideally we would only have `code : Q(ITree (EffB Γ) (Fin nBlocks))`, but we need to
  - Explicitly store the `assumes` in order to make non-deterministic `goto A, B, C;` deterministic (if possible).
    This could be avoided by using choice trees, and using effects for assumes instead (`AssumeAssert.lean`).
  - Store `gotos` because when one block gets elaborated individually, we don't know yet how many
    blocks there are and what their indices are.
    This could be avoided by storing a mapping from block label to `?idx : Fin ?N` in `BoogieElab`,
    which then get backfilled at the end of elaboration with the concrete indices.
-/
structure EBlock (Γ : Con) where
  label : TSyntax `ident
  /-- Any leading assumes for this block. -/
  assumes : Q(ITree (EffB $Γ) Bool)
  /-- Code without `assume`s and without `goto`s. -/
  code : Q(ITree (EffB $Γ) Unit)
  /-- The labels from `goto A, B, C;`. Empty list `[]` for `return;`.

    This is essentially `Array Name`, but having the syntax object is useful for
    `throwErrorAt gotoLabel "Unknown goto label"`. -/
  gotos : Array (TSyntax `ident)
deriving Inhabited, Repr

/-- An elaborated variable. This structure stores also some non-essential but precomputed stuff. -/
structure EVar (Γ : Con) where
  i : Fin Γ.length
  A : Ty := Γ.get i
  -- hA : Γ[i] = A
  v : Var Γ A -- := hA ▸ Var.ofIdx i
  vq : Q(Var $Γ $A) := q($v)
  -- Ah : Q($Γ[$i] = $A)
  -- vh : Q($vq = $Ah ▸ Var.ofIdx $i)
  deriving Repr

/-- Knowledge about the boogie program while elaborating the boogie syntax.
  You could remember all kinds of analysis in this monad, you'd potentially even have to. -/
structure BoogieElab (Γ : Con) where
  procName : Name
  /-- Mapping of names to de-Brujin indices, but also the type of the variable. -/
  varInfo : Std.HashMap Name (EVar Γ)
  -- nBlocks : Q(Nat)
  -- blockIndices : Std.HashMap Name Q(Fin $nBlocks) := {}
deriving Inhabited

abbrev BoogieElabM (Γ : Con) := StateT (BoogieElab Γ) TermElabM

private def logger [Monad m] [MonadTrace m] [MonadLiftT IO m] [MonadRef m] [AddMessageContext m]
  [MonadOptions m] {α : Type} [MonadAlwaysExcept Exception m] [MonadLiftT BaseIO m] [ToMessageData α]
  (fn : MessageData)
  (ok : {_ : α} -> MessageData := @fun val => m!"{val}")
  (err : {_ : Exception} -> MessageData := @fun e => m!"💥️ {e.toMessageData}")
  : Except Exception α → m MessageData
| .ok val => return m!"{fn} ~~> {@ok val}"
| .error e => return m!"{fn} ~~> {@err e}"

private def logger' [Monad m] [MonadTrace m] [MonadLiftT IO m] [MonadRef m] [AddMessageContext m]
  [MonadOptions m] {α : Type} [MonadAlwaysExcept Exception m] [MonadLiftT BaseIO m]
  (fn : MessageData)
  (ok : {_ : α} -> MessageData := "✓")
  (err : {_ : Exception} -> MessageData := @fun e => m!"💥️ {e.toMessageData}")
  : Except Exception α → m MessageData
| .ok val => return m!"{fn} ~~> {@ok val}"
| .error e => return m!"{fn} ~~> {@err e}"

def elabBoogieType : TSyntax `BoogieType -> TermElabM Ty
| `(BoogieType| int) => return Ty.int
| `(BoogieType| bool) => return Ty.bool
| `(BoogieType| bv1) => return Ty.bv 1
| `(BoogieType| bv2) => return Ty.bv 2
| `(BoogieType| bv4) => return Ty.bv 4
| `(BoogieType| bv8) => return Ty.bv 8
| `(BoogieType| bv16) => return Ty.bv 16
| `(BoogieType| bv32) => return Ty.bv 32
-- | `(BoogieType| bv$n) => do
--   let n : Q(Nat) <- Term.elabTermEnsuringType n q(Nat)
--   return q(BitVec $n)
| stx => throwError "elabBoogieType: Unknown syntax {stx}"

/-- Small convenience type. Often we want to store the source `Syntax` for a `Name` to be able
  to throw an error using `throwErrorAt stx`. -/
structure NameWithStx where
  stx : TSyntax `ident
abbrev NameWithStx.getId : NameWithStx -> Name := fun ⟨stx⟩ => stx.getId
-- instance : Coe (TSyntax `ident) NameWithStx where coe x := ⟨x⟩
instance : Coe NameWithStx (TSyntax `ident) where coe x := x.stx
instance : Coe NameWithStx Syntax where coe x := x.stx
instance : Coe NameWithStx Name where coe x := x.stx.getId
instance : BEq NameWithStx where beq a b := a.1.getId == b.1.getId
instance : Hashable NameWithStx where hash n := hash n.1.getId
instance : ToString NameWithStx where toString n := toString n.1.getId

local instance [BEq A] [Hashable A] [ToString A] : ToString (Std.HashSet A) where
  toString set := set.toList.toString

/-- Collect names of mutable (i.e. boogie) variables used in an expression. (Yes this is not very efficient) -/
partial def collectMutVars (stx : TSyntax `BoogieExpr) : MetaM (Std.HashSet NameWithStx) := do
  withRef stx (go stx)
where go
| `(BoogieExpr| $_n:num ) => return {}
| `(BoogieExpr| ( $x:BoogieExpr ) ) => collectMutVars x
| `(BoogieExpr| -$x:BoogieExpr) => collectMutVars x
| `(BoogieExpr| $x:BoogieExpr * $y:BoogieExpr) => return (<- collectMutVars x).union (<- collectMutVars y)
| `(BoogieExpr| $x:BoogieExpr + $y:BoogieExpr) => return (<- collectMutVars x).union (<- collectMutVars y)
| `(BoogieExpr| $x:BoogieExpr / $y:BoogieExpr) => return (<- collectMutVars x).union (<- collectMutVars y)
| `(BoogieExpr| $x:BoogieExpr - $y:BoogieExpr) => return (<- collectMutVars x).union (<- collectMutVars y)
| `(BoogieExpr| $x:BoogieExpr == $y:BoogieExpr) => return (<- collectMutVars x).union (<- collectMutVars y)
| `(BoogieExpr| $x:BoogieExpr <= $y:BoogieExpr) => return (<- collectMutVars x).union (<- collectMutVars y)
| `(BoogieExpr| $_f:ident($args,*)) =>
  -- note: we do not collect `f`, because functions can not be variables in boogie.
  args.getElems.foldlM (fun acc arg => return acc.union (<- collectMutVars arg)) {}
| `(BoogieExpr| $x:ident) => return {⟨x⟩}
  -- if (<- getThe BoogieElab).vars.contains x then return Std.HashSet.ofList [x]
  -- else throwError "collectMutVars: No such mutable variable {x}"
| stx => throwErrorAt stx "collectMutVars: Unknown syntax"

/-- Collect names of mutable (i.e. boogie) variables used in a formula. -/
partial def collectMutVarsFormula (stx : TSyntax `BoogieFormula) : MetaM (Std.HashSet NameWithStx) := do
  withRef stx (go stx)
where go
| `(BoogieFormula| ($x:BoogieFormula)) => collectMutVarsFormula x
| `(BoogieFormula| !$x:BoogieFormula) => collectMutVarsFormula x
| `(BoogieFormula| $x:BoogieExpr == $y:BoogieExpr) => return (<- collectMutVars x).union (<- collectMutVars y)
| `(BoogieFormula| $x:BoogieExpr <= $y:BoogieExpr) => return (<- collectMutVars x).union (<- collectMutVars y)
| `(BoogieFormula| $x:BoogieExpr < $y:BoogieExpr) => return (<- collectMutVars x).union (<- collectMutVars y)
| `(BoogieFormula| $x:BoogieFormula && $y:BoogieFormula) => return (<- collectMutVarsFormula x).union (<- collectMutVarsFormula y)
| `(BoogieFormula| $x:BoogieFormula || $y:BoogieFormula) => return (<- collectMutVarsFormula x).union (<- collectMutVarsFormula y)
| `(BoogieFormula| $x:BoogieFormula => $y:BoogieFormula) => return (<- collectMutVarsFormula x).union (<- collectMutVarsFormula y)
| stx => throwError "collectMutVarsFormula: Unknown syntax {stx}"

def lookupVar (varName : Name) : BoogieElabM Γ (Option (EVar Γ)) := do
  let res := (<- get).varInfo.get? varName
  return res

def getProcName : BoogieElabM Γ Name := do return (<- get).procName

/-- Read mutable variables from the boogie state monad, introducing them into the local context, and then run `m` in this new local context.
  Returns an expression like:
  ```
  bind (read "x") fun x =>
    bind (read "y") fun y =>
      /- whatever m evaluates to -/
  ``` -/
def withReadMutVars {Γ : Con} (vs : List NameWithStx) (X : Q(Type)) (m : BoogieElabM Γ Q(ITree (EffB $Γ) $X)) : BoogieElabM Γ Q(ITree (EffB $Γ) $X) := do
  match vs with
  | [] => m
  | v :: vs =>
    if let some { A, vq, .. } := <- lookupVar v then
      -- assertDefEq "(withReadMutVars) A ≡ Γ[i]" q($vTy) q(($Γ)[$i])
      -- let v : Q(Var $Γ $vTy) := (q(Var.ofIdx $vIdx) : Expr) -- okay because `Γ[vIdx] ≡ vTy`
      let a : Q(ITree (EffB $Γ) $A) := q(Mem.read $vq) -- here we use `embed` implicitly due to a coercion
      let b : Q($A -> ITree (EffB $Γ) $X) <- withLocalDeclDQ v.getId q($A) fun (v : Q($A)) => do
        let e : Q(ITree (EffB $Γ) $X) <- withReadMutVars vs X m
        mkLambdaFVars #[v] e
      return q(Bind.bind $a $b)
    else
      throwErrorAt v "withReadMutVars: Unknown variable"

mutual
  partial def elabBoogieExprPure' (stx : TSyntax `BoogieExpr) : BoogieElabM Γ ((A : Q(Type)) × Q($A)) := do
    let A <- mkFreshExprMVarQ q(Type)
    let e <- elabBoogieExprPure A stx
    return ⟨A, e⟩

  partial def elabBinOp (A : Q(Type)) (x y : TSyntax `BoogieExpr)
    (f : (X Y : Q(Type)) -> (x : Q($X)) -> (y : Q($Y)) -> BoogieElabM Γ Q($A))
    : BoogieElabM Γ Q($A)
    := do
    let ⟨X, x⟩ <- elabBoogieExprPure' x
    let ⟨Y, y⟩ <- elabBoogieExprPure' y
    f X Y x y

  partial def elabBinOpInst (A : Q(Type)) (x y : TSyntax `BoogieExpr)
    (Inst : (X Y : Q(Type)) -> Q(Type))
    (f : {X Y : Q(Type)} -> {_inst : Q($(Inst X Y))} -> (x : Q($X)) -> (y : Q($Y)) -> BoogieElabM Γ Q($A))
    : BoogieElabM Γ Q($A)
    := do
    let ⟨X, x⟩ <- elabBoogieExprPure' x
    let ⟨Y, y⟩ <- elabBoogieExprPure' y
    let inst <- mkInstMVar (Inst X Y)
    @f X Y inst x y

  /-- Evaluate a boogie expression, assuming that the Lean local context already contains variables
    which have been read from the boogie state monad, so assuming that we are within `withReadMutVars`. -/
  private partial def elabBoogieExprPure (A : Q(Type)) (stx : TSyntax `BoogieExpr) : BoogieElabM Γ Q($A) := do
    withTraceNode `LeanBoogie.dsl (logger m!"elabBoogieExprPure (A≡{A}) `{stx}`") do
      let ret <- withRef stx (go stx)
      let retTy <- inferType ret
      if !(<- isDefEq retTy A) then throwError "Expected {A} but got {retTy}"
      Term.addTermInfo' stx ret
      let ret <- instantiateExprMVars ret
      return ret
  where go
  | `(BoogieExpr| $n:num ) => do
    let n : Nat := n.getNat
    let ofnat : Q(OfNat $A $n) <- mkInstMVar q(OfNat $A $n)
    trace[LeanBoogie.dsl] "Have literal {n}, type is {A}, ofnat ≡ {ofnat}"
    have ret : Q($A) := q(($ofnat).ofNat)
    return ret
  | `(BoogieExpr| ( $x:BoogieExpr ) ) => elabBoogieExprPure A x
  | `(BoogieExpr| -$x:BoogieExpr)  => do
    let x <- elabBoogieExprPure q($A) x
    let _neg : Q(Neg $A) <- mkInstMVar q(Neg $A)
    return q(-$x)
  | `(BoogieExpr| $x:BoogieExpr * $y:BoogieExpr) => elabBinOpInst A x y (fun X Y => q(HMul $X $Y $A)) (fun x y => return q($x * $y))
  | `(BoogieExpr| $x:BoogieExpr / $y:BoogieExpr) => elabBinOpInst A x y (fun X Y => q(HDiv $X $Y $A)) (fun x y => return q($x / $y))
  | `(BoogieExpr| $x:BoogieExpr + $y:BoogieExpr) => elabBinOpInst A x y (fun X Y => q(HAdd $X $Y $A)) (fun x y => return q($x + $y))
  | `(BoogieExpr| $x:BoogieExpr - $y:BoogieExpr) => elabBinOpInst A x y (fun X Y => q(HSub $X $Y $A)) (fun x y => return q($x - $y))
  | `(BoogieExpr| $x:BoogieExpr == $y:BoogieExpr) => do
    let B <- mkFreshExprMVarQ q(Type)
    let x <- elabBoogieExprPure B x
    let y <- elabBoogieExprPure B y
    let deq <- mkInstMVar q(Decidable ($x = $y))
    have res : Q(Bool) := .app q(@decide ($x = $y)) deq
    return res
  | `(BoogieExpr| $x:BoogieExpr <= $y:BoogieExpr) => do
    if !(<- isDefEq A q(Bool)) then throwError "type must be Bool"
    let B : Q(Type) <- mkFreshExprMVarQ q(Type)
    let x <- elabBoogieExprPure B x
    let y <- elabBoogieExprPure B y
    let _leq <- synthInstanceQ q(LE $B)
    let deq <- synthInstanceQ q(Decidable ($x <= $y))
    have : Q(Bool) := q(@decide ($x <= $y) $deq)
    return this
  | stx@`(BoogieExpr| $f:ident($args,*)) => do
    let fn : Name <- realizeGlobalConstNoOverloadWithInfo f -- lookup name in Lean environment
    let fn : Expr <- mkConst fn

    let ⟨argMVars, argBi, fnType⟩ <- forallMetaTelescope (<- inferType fn)
    -- `argMVars` is for example `#[?n : Nat, ?x : BitVec ?n, ?y : BitVec ?n]`.
    -- Note how `?n` occurs in the expected type of subsequent mvars.
    let argMVars := argMVars.zip argBi |>.filter (·.snd == BinderInfo.default) |>.map Prod.fst -- only the explicit args (to fit `mkAppM`)
    -- now we want to assign each arg in `argMVars` to a concrete value, which we get from the syntax `args`.
    if args.getElems.size != argMVars.size then throwError m!"Expected {argMVars.size} explicit args for {fn}, but got {args.getElems.size}."
    args.getElems.zip argMVars |>.forM fun ⟨stx, mvar⟩ => do
      let B : Q(Type) <- inferType mvar
      let val <- elabBoogieExprPure B stx
      mvar.mvarId!.assign val
    let e <- mkAppM' fn argMVars
    if ¬(<- isDefEq fnType A) then throwErrorAt stx m!"Pure function application {stx} has type {fnType} but is expected to have type {A}"
    return e
  | `(BoogieExpr| $x:ident) => do
    let some ldecl := (<- getLCtx).findFromUserName? x.getId | throwError "elabBoogieExpr: No such local var {x.getId}"
    if !(<- isDefEq ldecl.type q($A)) then throwError "elabBoogieExpr: Local var {x.getId} has type {ldecl.type} but is expected to have type {A}"
    return ldecl.toExpr
  | stx => throwError "elabBoogieExprPure: Unknown syntax {stx}"

  /-- Given a boogie expression `x + y`, produces an expression `bind (get "x") (fun x => bind (get "y") (fun y => pure (x + y))) : ITree (EffB Γ) Int`. -/
  partial def elabBoogieExpr {Γ : Con} (A : Q(Type)) (stx : TSyntax `BoogieExpr) : BoogieElabM Γ Q(ITree (EffB $Γ) $A) := do
    withTraceNode `LeanBoogie.dsl (logger m!"elabBoogieExpr `{stx}`") do
      let vars <- collectMutVars stx
      trace[LeanBoogie.dsl] "collectMutVars returned {vars}"
      withReadMutVars vars.toList A (do
        let val : Q($A) <- elabBoogieExprPure A stx
        let m_val : Q(ITree (EffB $Γ) $A) := q(Pure.pure $val)
        return m_val
      )
end

partial def elabBoogieFormula (stx : TSyntax `BoogieFormula) : BoogieElabM Γ Q(Prop) := do
  withTraceNode `LeanBoogie.dsl (logger m!"elabBoogieFormula `{stx}`") do
    let ret <- withRef stx (go stx)
    Term.addTermInfo' stx ret
    return ret
where go
| `(BoogieFormula| ($x:BoogieFormula)) => elabBoogieFormula x
| `(BoogieFormula| !$x:BoogieFormula) => do
  let φ <- elabBoogieFormula x
  return q(Not $φ)
| `(BoogieFormula| $x:BoogieExpr == $y:BoogieExpr) => do
  let A <- mkFreshExprMVarQ q(Type)
  let x <- elabBoogieExprPure A x
  let y <- elabBoogieExprPure A y
  return q(Eq $x $y)
| `(BoogieFormula| $x:BoogieExpr < $y:BoogieExpr) => do
  let A <- mkFreshExprMVarQ q(Type)
  let x <- elabBoogieExprPure A x
  let y <- elabBoogieExprPure A y
  let _ <- synthInstanceQ q(LT $A)
  return q($x < $y)
| `(BoogieFormula| $x:BoogieExpr <= $y:BoogieExpr) => do
  let A <- mkFreshExprMVarQ q(Type)
  let x <- elabBoogieExprPure A x
  let y <- elabBoogieExprPure A y
  let _ <- synthInstanceQ q(LE $A)
  return q($x <= $y)
| `(BoogieFormula| $x:BoogieFormula && $y:BoogieFormula) => do
  let x <- elabBoogieFormula x
  let y <- elabBoogieFormula y
  return q($x ∧ $y)
| `(BoogieFormula| $x:BoogieFormula || $y:BoogieFormula) => do
  let x <- elabBoogieFormula x
  let y <- elabBoogieFormula y
  return q($x ∨ $y)
| `(BoogieFormula| $x:BoogieFormula => $y:BoogieFormula) => do
  let x <- elabBoogieFormula x
  let y <- elabBoogieFormula y
  return q($x -> $y)
| stx => throwError "elabBoogieFormula: Unknown syntax {stx}"

-- partial def elabBoogieAssume {Γ : Con} : TSyntax `BoogieAssume -> BoogieElabM Γ Q(ITree (EffB $Γ) Unit)
-- | stx@`(BoogieAssume| assume%$tok_assume $φ:BoogieFormula; ) => do
--   withTraceNode `LeanBoogie.dsl (logger m!"elabBoogieAssume `{stx}`") do
--     let vars <- collectMutVarsFormula φ
--     withReadMutVars vars.toList q(Unit) do
--       let φ : Q(Prop) <- elabBoogieFormula φ
--       let ret : Q(ITree (EffB $Γ) Unit) := q(LeanBoogie.assume $φ)
--       Term.addTermInfo' stx ret
--       Term.addTermInfo' tok_assume (ret.getBoundedAppFn 0)
--       return ret
-- | stx => throwError "elabBoogieAssume: Unknown syntax {stx}"

/-- Creates a program which decides the truth value of each assume, returns conjunction of that. -/
partial def elabBoogieAssume' {Γ : Con} : TSyntax `BoogieAssume -> BoogieElabM Γ Q(ITree (EffB $Γ) Bool)
| stx@`(BoogieAssume| assume $φ:BoogieFormula; ) => withRef stx do
  withTraceNode `LeanBoogie.dsl (logger m!"elabBoogieAssume' `{stx}`") do
    let vars <- collectMutVarsFormula φ
    withReadMutVars vars.toList q(Bool) do
      let φ : Q(Prop) <- elabBoogieFormula φ
      let dφ <- synthInstanceQ q(Decidable $φ) -- ! Need `Decidable`, or later: Use events
      let ret : Q(ITree (EffB $Γ) Bool) := q(return @decide $φ $dφ)
      return ret
| stx => throwError "elabBoogieAssume: Unknown syntax {stx}"

-- This is not in `BoogieElabM` because at this point we don't know the variables (and thus Γ) yet.
def elabBoogieVarBinder : TSyntax `BoogieVarBinder -> TermElabM (TSyntax `ident × Ty)
| stx@`(BoogieVarBinder| $id:ident : $type:BoogieType) => withRef stx do
  let ty : Ty <- elabBoogieType type
  Term.addTermInfo' type (<- whnf q($ty))
  return (id, ty)
| stx => throwError "elabBoogieVarBinder: Unknown syntax {stx}"

def elabBoogieVarBinders (binders: TSyntaxArray `BoogieVarBinder) : TermElabM (Array (TSyntax `ident × Ty)) := do
  binders.mapM elabBoogieVarBinder

def elabBoogieVarCmds (binders: TSyntaxArray `BoogieVarCmd) : TermElabM (Array (TSyntax `ident × Ty)) :=
  binders.mapM fun
    | `(BoogieVarCmd| var $b; ) => elabBoogieVarBinder b
    | stx => throwError "elabBoogieVarCmds: unknown syntax {stx}"

mutual
  /-- Elaborates a command such as `x := 2 * y;` or `while ... { ... }` into a monadic action. -/
  partial def elabBoogieCommand {Γ : Con} (stx : TSyntax `BoogieCommand) : BoogieElabM Γ Q(ITree (EffB $Γ) Unit) := do
    withTraceNode `LeanBoogie.dsl (logger m!"elabBoogieCommand `{stx}`") do
      withRef stx do
        withSynthesize do
          let ret <- go stx
          let ret <- instantiateExprMVarsQ ret
          Term.addTermInfo' stx ret
          return ret
  where go
  | `(BoogieCommand| $vName:ident := $e:BoogieExpr; ) => do
    if let some { A, vq, .. } := <- lookupVar vName.getId then
      let val : Q(ITree (EffB $Γ) $A) <- elabBoogieExpr q($A) e
      Term.addTermInfo' vName q($vq)
      let cmd : Q(ITree (EffB $Γ) Unit) := q(Bind.bind $val (fun val => Mem.write $vq val))
      return cmd
    else throwError "elabBoogieCommand: Unknown variable {vName}"
  | `(BoogieCommand| if $cond { $t* } $[else { $e* }]?) => do
    -- If you want to make this `if` dependent, you need to pull the mem gets (which `elabBoogieExpr`
    -- introduces for every referred-to var) in front of the entire `if`.
    let cond <- withRef cond <| elabBoogieExpr q(Bool) cond
    let t <- elabBoogieCommands t
    if let some e := e then
      let e <- elabBoogieCommands e
      return q(do if (<- $cond) then ($t) else ($e))
    else
      return q(do if (<- $cond) then ($t))
  | `(BoogieCommand| while $cond { $body* }) => do
    let cond <- withRef cond <| elabBoogieExpr q(Bool) cond
    let body <- elabBoogieCommands body
    return q(While $cond $body)
  | stx => throwError "elabBoogieCommand: Unknown syntax {stx}"

  partial def elabBoogieCommands {Γ : Con} (cmds : TSyntaxArray `BoogieCommand) : BoogieElabM Γ Q(ITree (EffB $Γ) Unit) := do
    cmds.foldlM (fun (acc : Q(ITree (EffB $Γ) Unit)) (cmd : TSyntax _) => do
      let cmd : Q(ITree (EffB $Γ) Unit) <- withRef cmd <| elabBoogieCommand cmd
      return q(do ($acc); ($cmd))
    ) q(return ())
end

def elabBoogieBlock {Γ : Con} : TSyntax `BoogieBlock -> BoogieElabM Γ (EBlock Γ)
| stx@`(BoogieBlock| $lbl:ident : $assumes:BoogieAssume* $cmds:BoogieCommand* $gotoOrReturn:BoogieBlockGotoOrReturn ) => do
  withTraceNode `LeanBoogie.dsl (logger' m!"elabBoogieBlock `{stx}`") do
    let lbl := lbl
    let assumes : Array Q(ITree (EffB $Γ) Bool) <- assumes.mapM elabBoogieAssume'
    let assumes : Q(ITree (EffB $Γ) Bool) :=
      -- We do this extra check to avoid putting `q(return true)` as the neutral element in the fold
      /- ! Side remark: These sort of handy little optimizations seem innocent, but they increase the
        amount of trusted code.  -/
      if h : assumes.size = 0 then q(return true)
      else assumes[1:].toArray.foldl (fun (acc a : Q(ITree (EffB $Γ) Bool)) =>
        q(do
          let acc <- ($acc)
          let a <- ($a)
          return acc && a
        ))
        assumes[0]
    -- logInfo "a"
    let cmds : Q(ITree (EffB $Γ) Unit) <- elabBoogieCommands cmds
    -- throwError "b, cmds := {cmds}"
    match gotoOrReturn with
    | `(BoogieBlockGotoOrReturn| goto $gotos,*;) =>
      -- let gotos : Array Name := gotos.getElems.map (fun g => g.getId)
      return ⟨lbl, assumes, cmds, gotos⟩
    | `(BoogieBlockGotoOrReturn| return;) =>
      return ⟨lbl, assumes, cmds, #[]⟩
    | _ => throwError "elabBoogieBlock: Unknown syntax {gotoOrReturn}"
| stx => throwError "elabBoogieBlock: Unknown syntax {stx}"

/-- Takes a bunch of pre-elaborated individual blocks, and ties them together with `iter`.

  If there are multiple goto labels `goto A, B, C;`, uses a choice effect to non-deterministically
  go to all labels simultaneously, and then uses an `assume` effect in each branch. -/
def wireUpBlocks {Γ : Con} (blocks : Array (EBlock Γ)) : BoogieElabM Γ Q(ITree (EffB $Γ) Unit) := sorry

/-- Adapter to turn `List (ITree ...)` into `Fin N -> ITree ...`, which is what `iter` expects. -/
def selectBlock {Γ : Con} (N : Nat) (blocks : List (ITree (EffB Γ) (Fin N ⊕ Unit))) (h : blocks.length = N)
  (i : Fin N) : ITree (EffB Γ) (Fin N ⊕ Unit)
  := blocks[i]

private def liftBlockToDef {Γ : Con} {N : Nat} (name : Name) (block : Q(ITree (EffB $Γ) (Fin $N ⊕ Unit))) : MetaM Q(ITree (EffB $Γ) (Fin $N ⊕ Unit))  := do
  let block <- instantiateMVars block
  let decl : DefinitionVal := {
    name
    levelParams := []
    type := <- inferType block
    value := block
    hints := .abbrev
    safety := .safe
  }
  addDecl (.defnDecl decl)
  return .const name []

/-- Takes a bunch of pre-elaborated individual blocks, and ties them together with `iter`.

  If there are multiple goto labels `goto A, B, C;` attempts to derive `Decidable` for each of `A`,
  `B`, and `C`'s leading `assume`s, and replaces the `goto A, B, C;` with `if`s accordingly.
  Problems:
  - This is not faithful to the Boogie spec, as we are choosing one of the possible program traces.
  - The `assume`s may not be decidable, so we can't represent all Boogie programs.

  A more faithful way of wiring up blocks would be using the `AmAt` effect, which allows you to
  assume and assert arbitrary statements, together with a choice effect or choice trees.
  However, then you have to interpret your programs into a Dijkstra monad, losing the nice
  computational properties. -/
def wireUpBlocksDeterministic {Γ : Con} (blocks : List (EBlock Γ)) (blocks_h : ¬blocks.length = 0)
  : BoogieElabM Γ Q(ITree (EffB $Γ) Unit)
  := do

  let N : Nat := blocks.length
  have hN : N = blocks.length := rfl
  let mut blockIndices : Std.HashMap Name (Fin N) := { }
  for h : (i : Nat) in [0 : N] do
    have h : i < N := by sorry
    blockIndices <- blockIndices.insertNewOrFail blocks[i].label.getId ⟨i, h⟩
      fun _ => throwErrorAt blocks[i].label "Duplicate block label"

  /- For each block, translate `goto A, B;` as (pseudocode):
  ```
  if (decide blocks["A"].assumes) then return .inl (index of blocks["A"])
  else if (decide blocks["B"].assumes) then return .inl (index of blocks["B"])
  else spin
  ```
  Recall that `.inl (block index here)` means continue execution at that block index, but `inr ()`
  means `return;` from the boogie procedure.
  -/
  let buildBlock (block : EBlock Γ) : BoogieElabM Γ Q(ITree (EffB $Γ) (Fin $N ⊕ Unit)) := do
    if block.gotos.isEmpty then
      -- `goto;` means `return;`, don't spin in that case
      return q(do ($block.code); return .inr ())
    else
      let decideBranch : Q(ITree (EffB $Γ) (Fin $N ⊕ Unit)) <- block.gotos.foldrM
        (fun gotoLabel acc => do
          let some (gotoIdx : Fin N) := blockIndices.get? gotoLabel.getId
            | throwErrorAt gotoLabel "Unknown block label"
          return q(do if <- $(blocks[gotoIdx].assumes) then return .inl ($gotoIdx) else ($acc))
        )
        q(spin) -- we could get rid of this `spin` if we can prove that always at least one of the assumes is true.
      return q(do ($block.code); ($decideBranch))

  let ns := (<- getCurrNamespace) ++ (<- getProcName)
  let blocks' : List Q(ITree (EffB «$Γ») (Fin «$N» ⊕ Unit)) <- blocks.mapM fun b => do
    let block <- buildBlock b
    liftBlockToDef (ns ++ b.label.getId) block
  have : blocks'.length = blocks.length := by sorry
  let ⟨blocks'', h⟩ := List.q_len N blocks' (this ▸ hN)
  let prf <- assumeQ q(0 < $N) -- this can be optimized
  return q(iter (selectBlock $N $(blocks'') $h) ⟨0, $prf⟩)

/-- Given an ITree which may refer to default-initialized local vars `L`, parameters `P`,
  obtain a `P -> ITree (Mem G) R`. -/
def runProc {P L : Con} {R : Type} (t : ITree (Mem (L ++ P)) R) (p : P) : ITree 0 R :=
  Prod.fst <$> interp' t ((default : L) ++ p)

/-- Given an ITree which may refer to default-initialized local vars `L`, parameters `P`, and
  global variables `G`, obtain a `P -> ITree (Mem G) R`. -/
def runProcGlobals {G P L : Con} {R : Ty} (t : ITree (Mem (L ++ P ++ G)) R) (p : P) : ITree (Mem G) R :=
  Prod.fst <$> interp' (Mem.split t) ((default : L) ++ p)

def runRes {A : Ty} (t : ITree (Mem ([A] ++ Γ)) Unit) (a : A) : ITree (Mem Γ) A :=
  (Prod.fst ∘ Prod.snd) <$> interp' (Mem.split t) (a, ())

abbrev TyA_or_Unit (A : Option Ty) : Type := A.map TyA |>.getD Unit

/-- Elaborated Boogie procedure. -/
structure EBoogieProc where
  name : Name
  /-- Global variables. -/
  G : Con
  /-- Return type. -/
  R : Option Ty
  /-- Parameters -/
  P : Con
  code : Q($P -> ITree (EffB $G) (TyA_or_Unit $R))

/-- Elab all arg, ret, and var binders, bundling them up into a `Γ : Con`. Also builds mapping
  from variable names to variable indices which is stored inside `BoogieElabM`. -/
def elabProcContext (stx : TSyntax `BoogieProc)
  (cont : (Γ : Con) ->
    (cmds : TSyntaxArray `BoogieCommand) ->
    (blocks : TSyntaxArray `BoogieBlock) ->
    (gotoOrReturn : Option <| TSyntax `LeanBoogie.BoogieBlockGotoOrReturn) ->
    BoogieElabM Γ Q(ITree (EffB $Γ) Unit)
  )
  : TermElabM EBoogieProc := do
  match stx with
  | `(BoogieProc| procedure $proc ( $argBinders,* ) $[returns ($retBinder)]? { $varBinders:BoogieVarCmd* $cmds:BoogieCommand* $[$gotoOrReturn:BoogieBlockGotoOrReturn]? $blocks:BoogieBlock* }) => do
    let argBinders <- argBinders.getElems.mapM fun (b : TSyntax _) => withRef b (elabBoogieVarBinder b)
    let P : Con := argBinders.map Prod.snd |>.toList
    let P_names := argBinders.map Prod.fst |>.toList

    let retBinder <- retBinder.mapM fun (b : TSyntax _) => withRef b (elabBoogieVarBinder b)
    let R : Option Ty := retBinder.map Prod.snd
    -- let R_names := retBinder.map Prod.fst

    let varBinders <- elabBoogieVarCmds varBinders
    let L : Con := varBinders.map Prod.snd |>.toList
    let L_names := varBinders.map Prod.fst |>.toList

    if let some R := R then
      let Γ : Con := [R] ++ L ++ P
      let Γ_names := [retBinder.map Prod.fst |>.get!] ++ L_names ++ P_names
      let varInfo <- buildVarInfo Γ_names (by sorry)
      let t : Q(ITree (EffB $Γ) Unit) <- StateT.run' (cont Γ cmds blocks gotoOrReturn) { procName := proc.getId, varInfo }
      let t : Q(ITree (EffB ($L ++ $P)) $R) := q(runRes $t default) -- `default`-initialize the return variable.
      let t : Q($P -> ITree 0 $R) := q(runProc $t)
      return { name := proc.getId, G := [], P, R := some R, code := t }
    else
      let Γ : Con := L ++ P
      let Γ_names := L_names ++ P_names
      let varInfo <- buildVarInfo Γ_names (by sorry)
      let t : Q(ITree (EffB $Γ) Unit) <- StateT.run' (cont Γ cmds blocks gotoOrReturn) { procName := proc.getId, varInfo }
      let t : Q($P -> ITree 0 Unit) := q(runProc $t)
      return { name := proc.getId, G := [], P, R := none, code := t }
  | stx => throwError "elabBoogieProcFrame: Unknown syntax {stx}"
where
  buildVarInfo {Γ} (names : List (TSyntax `ident)) (h : Γ.length = names.length) : TermElabM (Std.HashMap Name (EVar Γ)) := do
    let mut varInfo : Std.HashMap Name (EVar Γ) := {}
    for h : i in [0 : Γ.length] do -- surely this can be written nicer somehow?
      have h : i < Γ.length := by simp_all only [Membership.mem, zero_le, Array.toList_eq, Array.append_data, List.append_assoc, List.map_append, List.length_append, List.length_map, Array.data_length, true_and]
      varInfo <- varInfo.insertNewOrFail names[i]!.getId
        { i := ⟨i, h⟩, v := Var.ofIdx ⟨i, h⟩ }
        (@fun a => throwErrorAt names[i]! "Duplicate variable name {a} in {names}")
    return varInfo

def elabGotoOrReturn (stx : TSyntax `LeanBoogie.BoogieBlockGotoOrReturn) : TermElabM (Array (TSyntax `ident)) := do
  match stx with
  | `(BoogieBlockGotoOrReturn| goto $gotos,*;) => return gotos.getElems;
  | `(BoogieBlockGotoOrReturn| return;) => return #[]
  | _ => throwUnsupportedSyntax

def elabBoogieProc (stx : TSyntax `BoogieProc) : TermElabM EBoogieProc := do
  elabProcContext stx fun (Γ : Con) cmds blocks gotoOrReturn => do
    if h : blocks.size = 0 then
      -- No labels declared at all, in that case we don't need to set up blocky stuff at all.
      elabBoogieCommands cmds
    else
      let blocks <- blocks.mapM elabBoogieBlock
      let gotos : Array (TSyntax `ident) <- do
        if let some g := gotoOrReturn then elabGotoOrReturn g
        else pure #[(blocks[0]'sorry).label] -- sorry := h
      let leadingBlock : Array (EBlock Γ) <- do
        if ¬ cmds.isEmpty then
          pure #[{
            label := <- `(ident| _leadingBlock)
            assumes := q(return true)
            code := <- elabBoogieCommands cmds
            gotos := gotos
            : EBlock Γ
          }]
        else pure #[]
      let blocks := leadingBlock ++ blocks
      wireUpBlocksDeterministic blocks.toList sorry

/-
  ## Embedding Boogie syntax into Lean syntax.
  The star of the show.
  So far we've been living in our own `Boogie*` syntax categories, and now we hook it up to one of
  Lean's built-in syntax categories (e.g. `term`, `command`, `tactic`, etc).
-/

/-- A Boogie procedure, such as `procedure foo(x: int, y:int) { x := x + 10; }`.
  Gets elaborated into `def foo : ITree MemEv Unit := ...`, so an actual executable monadic program.

  You can run it via `runBoogie foo`, which gives you a `String -> Int`.
  Then you can read individual variables with `#eval (runBoogie foo) "x"`.
-/

elab stx:BoogieProc : command => do
  Command.liftTermElabM do
    let { name, G, R, P, code } <- elabBoogieProc stx
    let value <- instantiateMVars code
    let ty <- inferType value
    let decl : DefinitionVal := {
      name := (<- getCurrNamespace) ++ name
      type := ty
      value := <- instantiateMVars code
      levelParams := []
      hints := .abbrev
      safety := .safe
    }
    -- throwError "b"
    addDecl (.defnDecl decl)
    -- compileDecl (.defnDecl decl)

-- /-- Boogie Commands -/
-- elab "b{" cmds:BoogieCommand* "}" : term => runBoogieElab (elabBoogieCommands cmds)

-- /-- Boogie Block. -/
-- elab "bb{" cmds:BoogieCommand* gotos:BoogieGoto,* "}" : term =>
--   runBoogieElab do
--     let body <- elabBoogieCommands cmds
--     sorry

-- procedure foo(x: int, y: int) {
--   goto bb0;
--   bb0:
--     x := x + 20;
--     goto bb0, bb1;
--   bb1:
--     y := x + y;
--     goto bb0;
-- }

-- #print foo

-- set_option trace.LeanBoogie.dsl true

-- #exit

procedure test_func(x: int) returns (r: int) {
  var i : bv32;
}

#print test_func


procedure bar(y:int, x: int) {
  goto bb0;
  bb0:
    assume y == 10 && x <= 10;
    x := x + 10;
    goto bb1;
  bb1:
    x := x + 10;
    y := x + 10;
    goto bb0;
}

procedure baz(i: int) {
  i := 0;
  while i == 0 {
    i := i + 1;
  }
}

#print bar

-- procedure sum(n: int) returns (s: int) {
--   var i: int;
--   i := 0;
--   s := 0;
--   while (i <= n) {
--     i := i + 1;
--     s := s + i;
--   }
-- }

-- #print sum
-- example : sum = sorry := by
--   rw [sum]
--   simp

--   done

end Elab
