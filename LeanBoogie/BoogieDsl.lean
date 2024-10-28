import Lean
import Std
import Qq
import Aesop
import Init.Control.State
import Init.Control.Except
import LeanBoogie.Util
-- import LeanBoogie.ITree
import LeanBoogie.Boog
import Auto

namespace Boog
open Lean Elab Meta Qq
open Std (HashSet HashMap)

set_option auto.smt true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.printLemmas true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"

/-
  # Boogie DSL
-/

structure BoogieElab where
  nextVarId : Nat := 0
  /-- Mapping of mutable variable names to their ids. We use numeric IDs because lean-auto deals better with them than strings. -/
  vars : Std.HashMap Name Nat := {}

abbrev BoogieElabM := StateT BoogieElab TermElabM

def allocVarId : BoogieElabM Nat := modifyGetThe BoogieElab (fun s => (s.nextVarId, { s with nextVarId := s.nextVarId + 1}))

def declareVar (x : Name) : BoogieElabM Unit := do
  if (<- getThe BoogieElab).vars.contains x then
    throwError "Mutable variable {x} has already been declared"
  else
    let varId <- allocVarId
    modifyThe BoogieElab (fun s => { s with vars := s.vars.insert x varId})

-- ## Syntax

section Syntax
  declare_syntax_cat BoogieType
  syntax "unit" : BoogieType
  syntax "int" : BoogieType
  syntax "bool" : BoogieType

  declare_syntax_cat BoogieVarBinder
  syntax ident ": " BoogieType : BoogieVarBinder

  declare_syntax_cat BoogieExpr
  syntax:40 BoogieExpr " + " BoogieExpr : BoogieExpr
  syntax:40 BoogieExpr " - " BoogieExpr : BoogieExpr
  syntax:50 BoogieExpr " * " BoogieExpr : BoogieExpr
  syntax:50 BoogieExpr " / " BoogieExpr : BoogieExpr
  syntax:60 " -" BoogieExpr : BoogieExpr
  syntax ident : BoogieExpr -- variable
  syntax num : BoogieExpr -- literal
  syntax "(" BoogieExpr ")" : BoogieExpr
  syntax:30 BoogieExpr " <= " BoogieExpr : BoogieExpr
  syntax:30 BoogieExpr " == " BoogieExpr : BoogieExpr

  /-- Formulas can do things that boogie (boolean) expressions can't, e.g. forall quantifiers. -/
  declare_syntax_cat BoogieFormula
  syntax ident : BoogieFormula -- variables
  syntax BoogieExpr " <= " BoogieExpr : BoogieFormula
  syntax BoogieExpr " == " BoogieExpr : BoogieFormula
  syntax BoogieFormula " && " BoogieFormula : BoogieFormula
  syntax BoogieFormula " => " BoogieFormula : BoogieFormula

  declare_syntax_cat BoogieCommand
  syntax "var " BoogieVarBinder "; " : BoogieCommand
  syntax "assume " BoogieFormula "; " : BoogieCommand
  syntax ident " := " BoogieExpr "; " : BoogieCommand
  syntax "return " BoogieExpr "; " : BoogieCommand
  -- syntax "if " BoogieExpr " { " BoogieCommand* " }" : BoogieCommand
  syntax "if " BoogieExpr " { " BoogieCommand* " }" ("else" " { " BoogieCommand* " }")? : BoogieCommand
  syntax "while " BoogieExpr " { " BoogieCommand* " }" : BoogieCommand

  declare_syntax_cat BoogieProc
  syntax "procedure " ident "(" BoogieVarBinder,* ")" " returns " "(" BoogieVarBinder ")" " { " BoogieCommand* " }" : BoogieProc
end Syntax

-- ## Elaboration

section Elab

def elabBoogieType : TSyntax `BoogieType -> BoogieElabM Q(Type)
| `(BoogieType| int) => return q(Int)
| `(BoogieType| unit) => return q(Unit)
| `(BoogieType| bool) => return q(Bool)
| stx => throwError "elabBoogieType: Unknown syntax {stx}"

/-- With Lean 4.12 this hack won't be necessary. -/
def _root_.Std.HashSet.union [BEq A] [Hashable A] (a b : Std.HashSet A) : Std.HashSet A :=
  Std.HashSet.ofList (a.toList ++ b.toList)

/-- Collect names of mutable variables used in an expression. -/
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

/-- Read mutable variables from the boogie state monad, introducing them into the local context, and then run `m` in this new local context.
  Returns an expression like:
  ```
  bind (get "x") fun x =>
    bind (get "y") fun y =>
      /- whatever m evaluates to -/
  ``` -/
def withReadMutVars (vs : List Name) (A : Q(Type)) (m : BoogieElabM Q(Boog $A)) : BoogieElabM Q(Boog $A) := do
  match vs with
  | [] => m
  | v :: vs =>
    let vStr : String := v.toString
    let a : Q(Boog Int) := q(Boog.get $vStr)
    let b : Q(Int -> Boog $A) <- withLocalDeclDQ v q(Int) fun (v : Q(Int)) => do
      let e : Q(Boog $A) <- withReadMutVars vs A m
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

  /-- Given a boogie expression `x + y`, produces an expression `bind (get "x") (fun x => bind (get "y") (fun y => pure (x + y))) : Boog Int`. -/
  partial def elabBoogieExpr (A : Q(Type)) (stx : TSyntax `BoogieExpr) : BoogieElabM Q(Boog $A) := do
    let vars <- collectMutVars stx
    withReadMutVars vars.toList A (do
      let val : Q($A) <- elabBoogieExprPure A stx
      let m_val : Q(Boog $A) := q(Pure.pure $val)
      return m_val
    )
end

mutual
  partial def elabBoogieCommands (cmds : TSyntaxArray `BoogieCommand) : BoogieElabM Q(Boog Unit) := do
    cmds.foldlM (fun (acc : Q(Boog Unit)) (cmd : TSyntax _) => do
      let cmd : Q(Boog Unit) <- withRef cmd <| elabBoogieCommand cmd
      return q(Boog.seq $acc $cmd)
    ) q(Boog.skip)

  /-- Elaborates a command such as `x := 2 * y;` or `if ... { ... }` into a monadic action. -/
  partial def elabBoogieCommand : TSyntax `BoogieCommand -> BoogieElabM Q(Boog Unit)
  | _stx@`(BoogieCommand| $x:ident := $e:BoogieExpr; ) => do
    let val <- elabBoogieExpr q(Int) e
    let xStr : String := x.getId.toString
    let cmd : Q(Boog Unit) := q(Boog.set $xStr $val)
    -- Term.addTermInfo' stx cmd
    return cmd
  | `(BoogieCommand| if $cond { $t* } $[else { $e* }]?) => do
    let cond <- withRef cond <| elabBoogieExpr q(Bool) cond
    let t <- elabBoogieCommands t
    if let some e := e then
      let e <- elabBoogieCommands e
      return q(Boog.ifthenelse $cond $t $e)
    else
      return q(Boog.ifthen     $cond $t   )
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

/-- Elaborate a boogie procedure. You will usually pass a fresh metavar into `Ty`. Returns its name and body, also constrains the type `Ty`. -/
def elabBoogieProc : TSyntax `BoogieProc -> BoogieElabM (String × Q(Boog Unit))
| `(BoogieProc| procedure $proc ( $binders,* ) returns ($retBinder) { $body* }) => do
  let binders <- binders.getElems.mapM fun (b : TSyntax _) => withRef b <| do elabBoogieVarBinder b
  binders.forM fun (n, _ty) => declareVar n
  let (retVarName, _retVarType) <- withRef retBinder <| elabBoogieVarBinder retBinder
  declareVar retVarName
  return (proc.getId.toString, <- elabBoogieCommands body)
| stx => throwError "elabBoogieProc: Unknown syntax {stx}"

def runBoogieElab' (m : BoogieElabM A) : TermElabM (A × BoogieElab) := StateT.run m { }

def runBoogieElab (m : BoogieElabM A) : TermElabM A := Prod.fst <$> runBoogieElab' m

end Elab

/-- Actually execute a boogie program. -/
def runBoogie (m : Boog Unit) : BoogieState :=
  let s₀ : BoogieState := (fun _ => 0)
  let ((), s') := StateT.run m s₀
  s'

elab stx:BoogieProc : command => do
  Command.liftTermElabM do
    runBoogieElab do
      let (name, body) <- elabBoogieProc stx
      let decl : DefinitionVal := {
        name := (<- getCurrNamespace) ++ name.toName
        type := <- instantiateMVars q(Boog Unit)
        value := <- instantiateMVars body
        levelParams := []
        hints := .abbrev
        safety := .safe
      }
      addDecl (.defnDecl decl)
      compileDecl (.defnDecl decl)

theorem bind_eq2 (a: Boog A) (b: A -> Boog B) : (a >>= b : Boog B) = fun s => let x := a s ; b x.fst x.snd
:= by
  unfold bind Monad.toBind StateT.instMonad StateT.bind
  simp

@[aesop unsafe] theorem one_var {t1 t2 : String -> Int} (x : String)
  (h_x     : t1 x = t2 x)
  (h_other : (∀v, ¬ v = x -> t1 v = t2 v))
  : ∀v, t1 v = t2 v
  := by intro v; if h : x = v then exact h ▸ h_x else aesop

theorem ite_bind:
  ∀ [Monad m]
    [LawfulMonad m]
    {c : Bool}
    {m1 m2 : m a}
    {k : a -> m b},
   (if c then m1       else m2      ) >>= k
  = if c then m1 >>= k else m2 >>= k
  := by aesop

theorem var_congr_ite
  [Decidable c]
  (x : String)
  {t e t' e' : Boog A}
  (h_t :   c -> (t st).2 x = (t' st).2 x)
  (h_e : ¬ c -> (e st).2 x = (e' st).2 x)
  : ((if c then t else e) st).2 x = ((if c then t' else e') st).2 x
  -- : (prog1 st).2 x = (prog2 st).2 x
  := by aesop

namespace Example1
  procedure test1(x: int, y: int) returns (z: int) {
    x := (x + 1); x := x + 2;
    y := y + 1; y := y + 2;
    z := x + y;
  }
  procedure test2(x: int, y: int) returns (z: int) {
    y := y + 1; y := y + 2;
    x := x + 2; x := x + 1;
    z := x + y;
  }

  example (state) : test1 state = test2 state := by
    unfold BoogieState at state
    rw [test1, test2]
    simp [Boog.skip, Boog.set, Boog.get, Boog.set, Boog.seq, Boog.ifthen, Boog.ifthenelse,
      bind_eq2,
      StateT.get, StateT.set, getThe, modifyThe, StateT.modifyGet,
      pure, StateT.pure, instMonadStateOfMonadStateOf, instMonadStateOfStateTOfMonad]
    congr 1
    funext v -- for all vars..
    auto
end Example1



namespace Example2
  procedure square(x: int) returns (z : int) {
    if x <= 0 { x := -x; }
    y := 10;
    x := x * x;
  }
  procedure square'(x: int) returns (z : int) {
    x := x * x;
    y := 10;
  }

  -- set_option pp.explicit true in
  example (state) : square state = square' state := by
    unfold BoogieState at *
    rw [square, square']
    simp [Boog.skip, Boog.set, Boog.get, Boog.set, Boog.seq, Boog.ifthen, Boog.ifthenelse,
      bind_eq2, ↓ite_bind,
      StateT.get, StateT.set, getThe, modifyThe, StateT.modifyGet,
      pure, StateT.pure, instMonadStateOfMonadStateOf, instMonadStateOfStateTOfMonad, ↓reduceIte]
    congr 1
    funext x
    unfold BoogieState
    auto
    done
end Example2


namespace Example3
  procedure abs(x: int) returns (z : int) {
    if x <= 0 { x := -x; }
  }
  procedure abs'(x: int, y: int) returns (z : int) {
    if x <= 0 {
      y := x;
      x := x * x;
      x := x / y;
    }
  }

  example (state) : (abs state).2 "x" = (abs' state).2 "x" := by
    unfold BoogieState at state
    rw [abs, abs']
    simp [Boog.skip, Boog.set, Boog.get, Boog.set, Boog.seq, Boog.ifthen, Boog.ifthenelse,
      bind_eq2, ↓ite_bind,
      StateT.get, StateT.set, getThe, modifyThe, StateT.modifyGet,
      pure, StateT.pure, instMonadStateOfMonadStateOf, instMonadStateOfStateTOfMonad, ↓reduceIte]
    apply var_congr_ite "x" ?hx ?h'
    .
      intro h

      auto
    . aesop
      auto
end Example3
