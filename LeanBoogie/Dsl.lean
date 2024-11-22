import Lean
import Std
import Qq
import LeanBoogie.ITree
import LeanBoogie.Boogie
import LeanBoogie.Mem
import Batteries.Data.Array.Monadic

namespace LeanBoogie
open Lean Elab Meta Qq
open Std (HashSet HashMap)

open ITree

/-
  # Boogie DSL
  There's an official Lean guide here: https://leanprover-community.github.io/lean4-metaprogramming-book/main/08_dsls.html
-/

/-- An elaborated boogie block. -/
structure EBlock where
  label : String
  /-- Any leading assumes for this block. -/
  assumes : Q(ITree MemEv Bool)
  /-- Code without the assumes or gotos. -/
  code : Q(ITree MemEv Unit)
  /-- The labels from `goto A, B, C;`. Empty list `[]` for `return;`. -/
  gotos : Array String
deriving Inhabited, Repr

/-- Knowledge about the boogie program while elaborating the boogie syntax.
  You could remember all kinds of analysis in this monad, you'd potentially even have to. -/
structure BoogieElab where
  /-- Mapping of mutable variable names to their ids. Later: Also remember their type. -/
  vars : Std.HashSet Name := {}
  blocks : Array EBlock := #[]
deriving Inhabited


abbrev BoogieElabM := StateT BoogieElab TermElabM

def declareVar (x : Name) : BoogieElabM Unit := do
  if (<- getThe BoogieElab).vars.contains x then throwError "Mutable variable {x} has already been declared"
  else modifyThe BoogieElab (fun s => { s with vars := s.vars.insert x })



-- ## Syntax

section Syntax
  syntax BoogieIdent := ("$" noWs)? ident

  declare_syntax_cat BoogieType
  syntax "unit" : BoogieType
  syntax "int" : BoogieType
  syntax "bool" : BoogieType
  -- syntax "bv" noWs num : BoogieType -- Can we get something like this to work?
  syntax "bv32" : BoogieType
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

  declare_syntax_cat BoogieCommand
  syntax ident " := " BoogieExpr "; " : BoogieCommand
  syntax "if " BoogieExpr " { " BoogieCommand* " }" ("else" " { " BoogieCommand* " }")? : BoogieCommand
  syntax "while " BoogieExpr " { " BoogieCommand* " }" : BoogieCommand
  -- syntax "call " BoogieIdent "(" BoogieExpr,* ")" "; " : BoogieCommand
  -- syntax "var " BoogieVarBinder "; " : BoogieCommand
  -- syntax "assume " BoogieFormula "; " : BoogieCommand
  -- syntax "return " BoogieExpr "; " : BoogieCommand

  declare_syntax_cat BoogieAssume
  syntax "assume " BoogieFormula "; " : BoogieAssume
  declare_syntax_cat BoogieGoto
  syntax "goto " ident,* "; " : BoogieGoto -- once `return`s work, change this `*` into a `+`
  declare_syntax_cat BoogieReturn
  syntax "return" "; " : BoogieReturn

  declare_syntax_cat BoogieBlock
  syntax ident ": " BoogieAssume* BoogieCommand* (BoogieGoto <|> BoogieReturn) : BoogieBlock

  declare_syntax_cat BoogieVarCmd
  syntax "var " BoogieVarBinder "; " : BoogieVarCmd

  declare_syntax_cat BoogieProc
  syntax "procedure " ident "(" BoogieVarBinder,* ")" (" returns " "(" BoogieVarBinder ")")?
    " { "
      BoogieVarCmd*
      BoogieBlock*
    " }" : BoogieProc
end Syntax








/-
  ## Elaboration
  Takes `Lean.Syntax` (or, well, `Lean.TSyntax`) and spits out `Lean.Expr`.
-/

section Elab

def elabBoogieType : TSyntax `BoogieType -> BoogieElabM Q(Type)
| `(BoogieType| int) => return q(Int)
| `(BoogieType| unit) => return q(Unit)
| `(BoogieType| bool) => return q(Bool)
| `(BoogieType| bv1) => return q(BitVec 1)
| `(BoogieType| bv32) => return q(BitVec 32)
-- | `(BoogieType| bv$n) => do
--   let n : Q(Nat) <- Term.elabTermEnsuringType n q(Nat)
--   return q(BitVec $n)
| stx => throwError "elabBoogieType: Unknown syntax {stx}"

/-- Collect names of mutable (i.e. boogie) variables used in an expression. (Yes this is not very efficient) -/
partial def collectMutVars (stx : TSyntax `BoogieExpr) : BoogieElabM (Std.HashSet Name) := do
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
| `(BoogieExpr| $f:ident($args,*)) => args.getElems.foldlM (fun acc arg => return acc.union (<- collectMutVars arg)) {f.getId}
| `(BoogieExpr| $x:ident) => do
  let x := x.getId
  if (<- getThe BoogieElab).vars.contains x then return Std.HashSet.ofList [x]
  else throwError "collectMutVars: No such mutable variable {x}"
| stx => throwError "collectMutVars: Unknown syntax {stx}"

/-- Collect names of mutable (i.e. boogie) variables used in a formula. -/
partial def collectMutVarsFormula (stx : TSyntax `BoogieFormula) : BoogieElabM (Std.HashSet Name) := do
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

/-- Read mutable variables from the boogie state monad, introducing them into the local context, and then run `m` in this new local context.
  Returns an expression like:
  ```
  bind (get "x") fun x =>
    bind (get "y") fun y =>
      /- whatever m evaluates to -/
  ``` -/
def withReadMutVars (vs : List Name) (A : Q(Type)) (m : BoogieElabM Q(ITree MemEv $A)) : BoogieElabM Q(ITree MemEv $A) := do
  match vs with
  | [] => m
  | v :: vs =>
    let vStr : String := v.toString
    let a : Q(ITree MemEv Int) := q(Mem.read $vStr)
    let b : Q(Int -> ITree MemEv $A) <- withLocalDeclDQ v q(Int) fun (v : Q(Int)) => do
      let e : Q(ITree MemEv $A) <- withReadMutVars vs A m
      mkLambdaFVars #[v] e
    return q(Bind.bind $a $b)

mutual
  partial def elabBinOp (A B B' : Q(Type)) (x y : TSyntax `BoogieExpr) (f : Q($A) -> Q($A) -> Q($B)) : BoogieElabM Q($B) := do
    if !(<- isDefEq B B') then throwError "elabBinOp: {B} not defeq to {B'}"
    let x <- elabBoogieExprPure A x
    let y <- elabBoogieExprPure A y
    return f x y

  partial def elabBinOpM (A B B' : Q(Type)) (x y : TSyntax `BoogieExpr) (f : Q($A) -> Q($A) -> BoogieElabM Q($B)) : BoogieElabM Q($B) := do
    if !(<- isDefEq B B') then throwError "elabBinOpM: {B} not defeq to {B'}"
    let x <- elabBoogieExprPure A x
    let y <- elabBoogieExprPure A y
    f x y

  /-- Evaluate a boogie expression, assuming that the Lean local context already contains variables
    which have been read from the boogie state monad, so assuming that we are within `withReadMutVars`. -/
  private partial def elabBoogieExprPure (A : Q(Type)) (stx : TSyntax `BoogieExpr) : BoogieElabM Q($A) := do
    let ret <- withRef stx (go stx)
    let retTy <- inferType ret
    if !(<- isDefEq retTy A) then throwError "Expected {A} but got {retTy}"
    Term.addTermInfo' stx ret
    return ret
  where go
  | `(BoogieExpr| $n:num ) => do
    let n : Nat := n.getNat
    if !(<- isDefEq A q(Int)) then throwError "elabBoogieExpr: type must be int for int literals"
    have ret : Q(Int) := q(Int.ofNat $n)
    return ret
  | `(BoogieExpr| ( $x:BoogieExpr ) ) => elabBoogieExprPure A x
  | `(BoogieExpr| -$x:BoogieExpr)  => do
    if !(<- isDefEq A q(Int)) then throwError "elabBoogieExpr: type must be int"
    let x <- elabBoogieExprPure q(Int) x
    return (q(-$x) : Q(Int))
  | `(BoogieExpr| $x:BoogieExpr * $y:BoogieExpr)  => elabBinOp q(Int) q(Int) A x y (fun x y => q($x * $y))
  | `(BoogieExpr| $x:BoogieExpr / $y:BoogieExpr)  => elabBinOp q(Int) q(Int) A x y (fun x y => q($x / $y))
  | `(BoogieExpr| $x:BoogieExpr + $y:BoogieExpr)  => elabBinOp q(Int) q(Int) A x y (fun x y => q($x + $y))
  | `(BoogieExpr| $x:BoogieExpr - $y:BoogieExpr)  => elabBinOp q(Int) q(Int) A x y (fun x y => q($x - $y))
  | `(BoogieExpr| $x:BoogieExpr == $y:BoogieExpr) => do elabBinOpM (<- mkFreshExprMVarQ q(Type)) A A x y fun x y => do
    let deq <- synthInstanceQ q(Decidable ($x = $y))
    have : Q(Bool) := q(@decide ($x = $y) $deq)
    return this
  | `(BoogieExpr| $x:BoogieExpr <= $y:BoogieExpr) => do
    if !(<- isDefEq A q(Bool)) then throwError "elabBoogieExpr: type must be Bool"
    let B : Q(Type) <- mkFreshExprMVarQ q(Type)
    let x <- elabBoogieExprPure B x
    let y <- elabBoogieExprPure B y
    let _leq <- synthInstanceQ q(LE $B)
    let deq <- synthInstanceQ q(Decidable ($x <= $y))
    have : Q(Bool) := q(@decide ($x <= $y) $deq)
    return this
  | stx@`(BoogieExpr| $f:ident($args,*)) => do
    let fn <- realizeGlobalConstNoOverloadWithInfo f -- lookup function
    let args <- args.getElems.mapM (elabBoogieExprPure (<- mkFreshExprMVar none))
    let e <- mkAppM fn args
    let eTy <- inferType e
    if ¬(<- isDefEq eTy A) then throwErrorAt stx m!"Pure function application {stx} has type {eTy} but is expected to have type {A}"
    return e
  | `(BoogieExpr| $x:ident) => do
    let some ldecl := (<- getLCtx).findFromUserName? x.getId | throwError "elabBoogieExpr: No such local var {x.getId}"
    if !(<- isDefEq ldecl.type q($A)) then throwError "elabBoogieExpr: Local var {x.getId} has type {ldecl.type} but is expected to have type {A}"
    return ldecl.toExpr
  | stx => throwError "elabBoogieExprPure: Unknown syntax {stx}"

  /-- Given a boogie expression `x + y`, produces an expression `bind (get "x") (fun x => bind (get "y") (fun y => pure (x + y))) : ITree MemEv Int`. -/
  partial def elabBoogieExpr (A : Q(Type)) (stx : TSyntax `BoogieExpr) : BoogieElabM Q(ITree MemEv $A) := do
    let vars <- collectMutVars stx
    withReadMutVars vars.toList A (do
      let val : Q($A) <- elabBoogieExprPure A stx
      let m_val : Q(ITree MemEv $A) := q(Pure.pure $val)
      return m_val
    )
end

partial def elabBoogieFormula (stx : TSyntax `BoogieFormula) : BoogieElabM Q(Prop) := do
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

partial def elabBoogieAssume : TSyntax `BoogieAssume -> BoogieElabM Q(ITree MemEv Unit)
| stx@`(BoogieAssume| assume $φ:BoogieFormula; ) => do
  let vars <- collectMutVarsFormula φ
  withReadMutVars vars.toList q(Unit) do
    let φ : Q(Prop) <- elabBoogieFormula φ
    let _dφ <- synthInstanceQ q(Decidable $φ) -- ! Need `Decidable`, or later: Use events
    -- have : Q(Bool) := q(@decide $φ $dφ)
    let ret : Q(ITree MemEv Unit) := q(ITree.assume $φ)
    Term.addTermInfo' stx ret
    return ret
| stx => throwError "elabBoogieAssume: Unknown syntax {stx}"

/-- Creates a program which decides the truth value of each assume, returns conjunction of that. -/
partial def elabBoogieAssume' : TSyntax `BoogieAssume -> BoogieElabM Q(ITree MemEv Bool)
| _stx@`(BoogieAssume| assume $φ:BoogieFormula; ) => do
  let vars <- collectMutVarsFormula φ
  withReadMutVars vars.toList q(Bool) do
    let φ : Q(Prop) <- elabBoogieFormula φ
    let dφ <- synthInstanceQ q(Decidable $φ) -- ! Need `Decidable`, or later: Use events
    let ret : Q(ITree MemEv Bool) := q(return @decide $φ $dφ)
    return ret
    -- return q(.ret (decide $φ))
| stx => throwError "elabBoogieAssume: Unknown syntax {stx}"


def elabBoogieVarBinder : TSyntax `BoogieVarBinder -> BoogieElabM (Name × Q(Type))
| `(BoogieVarBinder| $id:ident : $type:BoogieType) => do
  let ty <- elabBoogieType type
  Term.addTermInfo' type ty
  return (id.getId, ty)
| stx => throwError "elabBoogieVarBinder: Unknown syntax {stx}"

def elabBoogieVarBinders (binders: TSyntaxArray `BoogieVarBinder) : BoogieElabM (Array <| Name × Q(Type)) := do
  binders.mapM elabBoogieVarBinder

def elabBoogieVarCmds (binders: TSyntaxArray `BoogieVarCmd) : BoogieElabM (Array <| Name × Q(Type)) :=
  binders.mapM fun
    | `(BoogieVarCmd| var $b; ) => elabBoogieVarBinder b
    | stx => throwError "elabBoogieVarCmds: unknown syntax {stx}"

mutual
  partial def elabBoogieCommands (cmds : TSyntaxArray `BoogieCommand) : BoogieElabM Q(ITree MemEv Unit) := do
    cmds.foldlM (fun (acc : Q(ITree MemEv Unit)) (cmd : TSyntax _) => do
      let cmd : Q(ITree MemEv Unit) <- withRef cmd <| elabBoogieCommand cmd
      return q(.seq $acc $cmd)
    ) q(Pure.pure ())

  /-- Elaborates a command such as `x := 2 * y;` or `if ... { ... }` into a monadic action. -/
  partial def elabBoogieCommand (stx : TSyntax `BoogieCommand) : BoogieElabM Q(ITree MemEv Unit) := do
    let ret <- withRef stx (go stx)
    Term.addTermInfo' stx ret
    return ret
  where go
  | _stx@`(BoogieCommand| $x:ident := $e:BoogieExpr; ) => do
    let val <- elabBoogieExpr q(Int) e
    let xStr : String := x.getId.toString
    let cmd : Q(ITree MemEv Unit) := q(Bind.bind $val (fun val => Mem.write $xStr val))
    -- Term.addTermInfo' stx cmd
    return cmd
  | `(BoogieCommand| if $cond { $t* } $[else { $e* }]?) => do
    -- If you want to make this `if` dependent, you need to pull the mem gets in front of the if.
    let cond <- withRef cond <| elabBoogieExpr q(Bool) cond
    let t <- elabBoogieCommands t
    if let some e := e then
      let e <- elabBoogieCommands e
      return q(ITree.ite $cond $t $e)
    else
      return q(ITree.ifthen $cond $t)
  | `(BoogieCommand| while $cond { $body* }) => do
    let _cond <- withRef cond <| elabBoogieExpr q(Bool) cond
    let _body <- elabBoogieCommands body
    throwError "while loops not yet implemented"
  | stx => throwError "elabBoogieCommand: Unknown syntax {stx}"
end

def elabBoogieBlock : TSyntax `BoogieBlock -> BoogieElabM EBlock
| `(BoogieBlock| $lbl:ident : $assumes:BoogieAssume* $cmds:BoogieCommand* goto $gotos,* ; ) => do
  let lbl := lbl.getId.toString
  let assumes : Array Q(ITree MemEv Bool) <- assumes.mapM elabBoogieAssume'
  let assumes : Q(ITree MemEv Bool) := assumes.foldl (fun (acc a : Q(ITree MemEv Bool)) =>
    q(do
      let acc <- ($acc)
      let a <- ($a)
      return acc && a
    ))
    q(return true)
  let cmds : Q(ITree MemEv Unit) <- elabBoogieCommands cmds
  let gotos : Array String := gotos.getElems.map (fun g => g.getId.toString)
  return ⟨lbl, assumes, cmds, gotos⟩
| `(BoogieBlock| $lbl:ident : $assumes:BoogieAssume* $cmds:BoogieCommand* return%$rtk ; ) => do
  throwErrorAt rtk "returns not yet supported, use `goto;`"
| stx => throwError "elabBoogieBlock: Unknown syntax {stx}"


structure EBoogieProc where
  name : String
  /-- Amount of labels -/
  N : Nat
  body : Q(ITree MemEv Unit)

/-- Adapter to turn `List (ITree ...)` into `Fin N -> ITree ...`, which is what `iter` expects. -/
def selectBlock (N : Nat) (blocks : List (ITree MemEv (Fin N ⊕ Unit))) (h : blocks.length = N) (i : Fin N)
  : ITree MemEv (Fin N ⊕ Unit)
  := blocks[i]

/-- Elaborate a boogie procedure. Returns the procedure name and its body. -/
def elabBoogieProc : TSyntax `BoogieProc -> BoogieElabM EBoogieProc
| `(BoogieProc| procedure $proc ( $binders,* ) $[returns ($retBinder)]? { $vars:BoogieVarCmd* $body:BoogieBlock* }) => do
  -- vars: parameters
  let binders <- binders.getElems.mapM fun (b : TSyntax _) => withRef b <| do elabBoogieVarBinder b
  binders.forM fun (n, _ty) => declareVar n
  -- vars: ret var
  if let some retBinder := retBinder then
    let (retVarName, _retVarType) <- withRef retBinder <| elabBoogieVarBinder retBinder
    declareVar retVarName
  -- vars: local procedure vars
  let locals <- elabBoogieVarCmds vars
  locals.forM fun (n, _ty) => declareVar n

  let blocks : Array EBlock <- body.mapM elabBoogieBlock
  let blocksSorted := blocks.insertionSort (fun a b => a.label < b.label)
  if ¬ (blocksSorted.dedupSorted (eq := ⟨fun a b => a.label == b.label⟩)).size = blocks.size
    then throwError "Duplicate block labels"

  let blocks := blocks.toList
  let N : Nat := blocks.length -- amount of labels -- * Here `N` is blocks.length definitionally
  if N_0 : N = 0
    then throwError "Need at least one block."
  else
    have q_N : Q(Nat) := q($N)
    have q_N_0 : Q(¬ $q_N = 0) := sorry
    have q_N_0 : Q(0 < $q_N) := q(by omega)

    /- For each block, translate `goto A, B;` as (pseudocode):
    ```
    if (decide blocks["A"].assumes) then return .inl (index of blocks["A"])
    else if (decide blocks["B"].assumes) then return .inl (index of blocks["B"])
    else spin
    ```
    Recall that `.inl (block index here)` means continue execution at that block index, but `inr ()`
    means `return;` from the boogie procedure.
    -/
    let f : EBlock -> Q(ITree MemEv (Fin $N ⊕ Unit)) := fun b =>
      let brancher : Q(ITree MemEv (Fin $N ⊕ Unit)) := b.gotos.foldr (fun g brancher =>
        if let .some g_block_idx := blocks.findIdxH? (le_refl N) (fun b => b.label == g) then -- translate string label e.g. `bb1` into block index.
          -- | throwError "Block {b.label} goes to unknown label {g}"
          let g_block := blocks[g_block_idx]
          q(do if <- $(g_block.assumes) then return .inl $g_block_idx else ($brancher)) -- (!) decide the `assume`
        else panic! s!"Block {b.label} goes to unknown label {g}"
      ) q(spin)
      if b.gotos.isEmpty then q(do ($b.code); return .inr ()) -- `goto;` means `return;`, don't spin in that case
      else q(do ($b.code); ($brancher))

    let blocks' : List Q(ITree MemEv (Fin $N ⊕ Unit)) := blocks.map f
    let h_blocks' : blocks'.length = blocks.length := blocks.length_map f
    -- let xx : SatisfiesM (fun arr => arr.size = blocks.size) (blocks.mapM f) := blocks.size_mapM f

    let blocks'' : Q((xs : List (ITree MemEv (Fin $N ⊕ Unit))) ×' xs.length = $N) := List.q_len N blocks' (by omega)
    -- let q_blocks : Q(List (ITree MemEv (Fin $N ⊕ Unit))) := q($blocks''.1)
    -- let q_blocks_len : Q(($q_blocks).length = $N) := q($blocks''.2)
    -- let q_blocks_notEmpty :
    let blocks''' : Q(Fin $N -> ITree MemEv (Fin $N ⊕ Unit)) := q(selectBlock $N $blocks''.1 $blocks''.2)
    -- let q_n_0 : Q()
    return {
      name := proc.getId.toString
      N := N
      body := q(ITree.iter (A := Fin $N) (B := Unit) $blocks''' ⟨0, sorry⟩) -- This is "just" `q_N_0`.
    }
| stx => throwError "elabBoogieProc: Unknown syntax {stx}"

def runBoogieElab' (m : BoogieElabM A) : TermElabM (A × BoogieElab) := StateT.run m { }
def runBoogieElab  (m : BoogieElabM A) : TermElabM A := Prod.fst <$> runBoogieElab' m

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
    runBoogieElab do
      let ⟨name, _N, body⟩ <- elabBoogieProc stx
      let decl : DefinitionVal := {
        name := (<- getCurrNamespace) ++ name.toName
        type := q(ITree MemEv Unit)
        value := <- instantiateMVars body
        levelParams := []
        hints := .abbrev
        safety := .safe
      }
      addDecl (.defnDecl decl)
      compileDecl (.defnDecl decl)

/-- Boogie Commands -/
elab "b{" cmds:BoogieCommand* "}" : term => runBoogieElab (elabBoogieCommands cmds)

-- /-- Boogie Block. -/
-- elab "bb{" cmds:BoogieCommand* gotos:BoogieGoto,* "}" : term =>
--   runBoogieElab do
--     let body <- elabBoogieCommands cmds
--     sorry

procedure foo(x: int, y: int) {
  bb0:
    x := x + 20;
    goto bb0, bb1;
  bb1:
    y := x + y;
    goto bb0;
}

procedure bar(x: int) {
  bb0:
    assume x == 10 && x <= 10;
    x := x + 10;
    goto bb1;
  bb1:
    y := x + 10;
    goto bb0;
}

end Elab
