import Lean
import Std
import Qq
-- import LeanBoogie.Boog
import LeanBoogie.ITree

namespace Boogie
open Lean Elab Meta Qq
open Std (HashSet HashMap)

/-
  # Boogie DSL
  There's an official Lean guide here: https://leanprover-community.github.io/lean4-metaprogramming-book/main/08_dsls.html
-/

/-- Knowledge about the boogie program while elaborating the boogie syntax.
  You could remember all kinds of analysis in this monad, you'd potentially even have to.
  Later: Also track jump labels / basic blocks. -/
structure BoogieElab where
  /-- Mapping of mutable variable names to their ids. Later: Also remember their type. -/
  vars : Std.HashSet Name := {}

abbrev BoogieElabM := StateT BoogieElab TermElabM

def declareVar (x : Name) : BoogieElabM Unit := do
  if (<- getThe BoogieElab).vars.contains x then
    throwError "Mutable variable {x} has already been declared"
  else
    modifyThe BoogieElab (fun s => { s with vars := s.vars.insert x })

-- ## Syntax

section Syntax
  declare_syntax_cat BoogieType
  syntax "unit" : BoogieType
  syntax "int" : BoogieType
  syntax "bool" : BoogieType

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
  syntax ident : BoogieExpr -- variable
  syntax num : BoogieExpr -- literal
  syntax "(" BoogieExpr ")" : BoogieExpr

  /-- Formulas can do things that boogie (boolean) expressions can't, e.g. forall quantifiers. -/
  declare_syntax_cat BoogieFormula
  syntax ident : BoogieFormula -- variables
  syntax:60 "(" BoogieFormula ")" : BoogieFormula
  syntax:60 " !" BoogieFormula : BoogieFormula
  syntax:50 BoogieExpr:max " <= " BoogieExpr:max : BoogieFormula
  syntax:50 BoogieExpr:max " == " BoogieExpr:max : BoogieFormula
  syntax:50 BoogieFormula " && " BoogieFormula : BoogieFormula
  syntax:40 BoogieFormula " || " BoogieFormula : BoogieFormula
  syntax:30 BoogieFormula " => " BoogieFormula : BoogieFormula
  syntax:20 "∀" ident ": " BoogieType ", " BoogieFormula : BoogieFormula

  declare_syntax_cat BoogieCommand
  syntax "var " BoogieVarBinder "; " : BoogieCommand
  syntax "assume " BoogieFormula "; " : BoogieCommand
  syntax ident " := " BoogieExpr "; " : BoogieCommand
  syntax "return " BoogieExpr "; " : BoogieCommand
  syntax "if " BoogieExpr " { " BoogieCommand* " }" ("else" " { " BoogieCommand* " }")? : BoogieCommand
  syntax "while " BoogieExpr " { " BoogieCommand* " }" : BoogieCommand

  declare_syntax_cat BoogieProc
  syntax "procedure " ident "(" BoogieVarBinder,* ")" (" returns " "(" BoogieVarBinder ")")? " { " BoogieCommand* " }" : BoogieProc
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
| stx => throwError "elabBoogieType: Unknown syntax {stx}"

/-- Collect names of mutable (i.e. boogie) variables used in an expression. -/
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
| stx => throwError "collectMutVarsFormula: Unknown syntax {stx}"

/-- Read mutable variables from the boogie state monad, introducing them into the local context, and then run `m` in this new local context.
  Returns an expression like:
  ```
  bind (get "x") fun x =>
    bind (get "y") fun y =>
      /- whatever m evaluates to -/
  ``` -/
def withReadMutVars (vs : List Name) (A : Q(Type)) (m : BoogieElabM Q(Mem $A)) : BoogieElabM Q(Mem $A) := do
  match vs with
  | [] => m
  | v :: vs =>
    let vStr : String := v.toString
    let a : Q(Mem Int) := q(Mem.get $vStr)
    let b : Q(Int -> Mem $A) <- withLocalDeclDQ v q(Int) fun (v : Q(Int)) => do
      let e : Q(Mem $A) <- withReadMutVars vs A m
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
  | `(BoogieExpr| $x:ident) => do
    let some ldecl := (<- getLCtx).findFromUserName? x.getId | throwError "elabBoogieExpr: No such local var {x.getId}"
    if !(<- isDefEq ldecl.type q($A)) then throwError "elabBoogieExpr: Local var {x.getId} has type {ldecl.type} but is expected to have type {A}"
    return ldecl.toExpr
  | stx => throwError "elabBoogieExprPure: Unknown syntax {stx}"

  /-- Given a boogie expression `x + y`, produces an expression `bind (get "x") (fun x => bind (get "y") (fun y => pure (x + y))) : Mem Int`. -/
  partial def elabBoogieExpr (A : Q(Type)) (stx : TSyntax `BoogieExpr) : BoogieElabM Q(Mem $A) := do
    let vars <- collectMutVars stx
    withReadMutVars vars.toList A (do
      let val : Q($A) <- elabBoogieExprPure A stx
      let m_val : Q(Mem $A) := q(Pure.pure $val)
      return m_val
    )
end

partial def elabBoogieFormula (stx : TSyntax `BoogieFormula) : BoogieElabM Q(Prop) := do
  withRef stx (go stx)
where go
| `(BoogieFormula| ($x:BoogieFormula)) => elabBoogieFormula x
| `(BoogieFormula| !$x:BoogieFormula) => do
  let φ <- elabBoogieFormula x
  return q(Not $φ)
| `(BoogieFormula| $x:BoogieExpr == $y:BoogieExpr) => do
  let A <- mkFreshExprMVarQ q(Type)
  let x <- elabBoogieExpr A x
  let y <- elabBoogieExpr A y
  return q(Eq $x $y)
| stx => throwError "elabBoogieFormula: Unknown syntax {stx}"

mutual
  partial def elabBoogieCommands (cmds : TSyntaxArray `BoogieCommand) : BoogieElabM Q(Mem Unit) := do
    cmds.foldlM (fun (acc : Q(Mem Unit)) (cmd : TSyntax _) => do
      let cmd : Q(Mem Unit) <- withRef cmd <| elabBoogieCommand cmd
      return q(.seq $acc $cmd)
    ) q(.skip)

  /-- Elaborates a command such as `x := 2 * y;` or `if ... { ... }` into a monadic action. -/
  partial def elabBoogieCommand : TSyntax `BoogieCommand -> BoogieElabM Q(Mem Unit)
  | _stx@`(BoogieCommand| $x:ident := $e:BoogieExpr; ) => do
    let val <- elabBoogieExpr q(Int) e
    let xStr : String := x.getId.toString
    let cmd : Q(Mem Unit) := q(bind $val (fun val => Mem.set $xStr val))
    -- Term.addTermInfo' stx cmd
    return cmd
  | `(BoogieCommand| assume $φ:BoogieFormula; ) => do
    let vars <- collectMutVarsFormula φ
    withReadMutVars vars.toList q(Unit) do
      let φ : Q(Prop) <- elabBoogieFormula φ
      let _dφ <- synthInstanceQ q(Decidable $φ) -- ! Need `Decidable`
      -- have : Q(Bool) := q(@decide $φ $dφ)
      return q(ITree.assume $φ) -- return q(if $φ then ITree.skip else ITree.spin)
  | `(BoogieCommand| if $cond { $t* } $[else { $e* }]?) => do
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

def elabBoogieVarBinder : TSyntax `BoogieVarBinder -> BoogieElabM (Name × Q(Type))
| `(BoogieVarBinder| $id:ident : $type:BoogieType) => do
  let ty <- elabBoogieType type
  Term.addTermInfo' type ty
  return (id.getId, ty)
| stx => throwError "elabBoogieVarBinder: Unknown syntax {stx}"

/-- Elaborate a boogie procedure. Returns the procedure name and its body. -/
def elabBoogieProc : TSyntax `BoogieProc -> BoogieElabM (String × Q(Mem Unit))
| `(BoogieProc| procedure $proc ( $binders,* ) $[returns ($retBinder)]? { $body* }) => do
  let binders <- binders.getElems.mapM fun (b : TSyntax _) => withRef b <| do elabBoogieVarBinder b
  binders.forM fun (n, _ty) => declareVar n
  if let some retBinder := retBinder then
    let (retVarName, _retVarType) <- withRef retBinder <| elabBoogieVarBinder retBinder
    declareVar retVarName
  return (proc.getId.toString, <- elabBoogieCommands body)
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
  Gets elaborated into `def foo : Mem Unit := ...`, so an actual executable monadic program.

  You can run it via `runBoogie foo`, which gives you a `String -> Int`.
  Then you can read individual variables with `#eval (runBoogie foo) "x"`.
-/
elab stx:BoogieProc : command => do
  Command.liftTermElabM do
    runBoogieElab do
      let (name, body) <- elabBoogieProc stx
      let decl : DefinitionVal := {
        name := (<- getCurrNamespace) ++ name.toName
        type := <- instantiateMVars q(Mem Unit)
        value := <- instantiateMVars body
        levelParams := []
        hints := .abbrev
        safety := .safe
      }
      addDecl (.defnDecl decl)
      compileDecl (.defnDecl decl)

procedure foo(x: int) { x := x + 10; }

#check ITree.run foo (fun _ => 0) 10
-- #eval! ITree.run foo (fun _ => 0) 10

end Elab
