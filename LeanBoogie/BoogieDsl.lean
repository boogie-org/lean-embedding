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
  vars : List Name := []

abbrev BoogieElabM := StateT BoogieElab TermElabM

def declareVar (x : Name) : BoogieElabM Unit := do
  if (<- getThe BoogieElab).vars.contains x then throwError "Mutable variable {x} has already been declared"
  else modifyThe BoogieElab (fun s => { s with vars := x :: s.vars })

-- ## Syntax

section Syntax
  declare_syntax_cat BoogieType
  syntax "unit" : BoogieType
  syntax "int" : BoogieType
  syntax "bool" : BoogieType

  declare_syntax_cat BoogieVarBinder
  syntax ident ": " BoogieType : BoogieVarBinder

  declare_syntax_cat BoogieExpr
  syntax BoogieExpr " + " BoogieExpr : BoogieExpr
  syntax BoogieExpr " * " BoogieExpr : BoogieExpr
  syntax ident : BoogieExpr -- variable
  syntax num : BoogieExpr -- literal
  syntax "(" BoogieExpr ")" : BoogieExpr
  syntax BoogieExpr " <= " BoogieExpr : BoogieExpr

  /-- Formulas can do things that boogie (boolean) expressions can't, e.g. forall quantifiers. -/
  declare_syntax_cat BoogieFormula
  syntax ident : BoogieFormula -- variables
  syntax BoogieExpr " <= " BoogieExpr : BoogieFormula
  syntax BoogieExpr " == " BoogieExpr : BoogieFormula
  syntax BoogieFormula " && " BoogieFormula : BoogieFormula
  syntax BoogieFormula " => " BoogieFormula : BoogieFormula

  declare_syntax_cat BoogieCommand
  syntax "var " ident " : " BoogieType ";" : BoogieCommand
  syntax "assume " BoogieFormula ";" : BoogieCommand
  syntax ident " := " BoogieExpr ";" : BoogieCommand
  syntax "return " BoogieExpr ";" : BoogieCommand
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
| _ => throwError "elabBoogieType exhausted"

/-- With Lean 4.12 this hack won't be necessary. -/
def _root_.Std.HashSet.union [BEq A] [Hashable A] (a b : Std.HashSet A) : Std.HashSet A :=
  Std.HashSet.ofList (a.toList ++ b.toList)

/-- Collect names of mutable variables used in an expression. -/
partial def collectMutVars : TSyntax `BoogieExpr -> BoogieElabM (Std.HashSet Name)
| `(BoogieExpr| $_n:num ) => return {}
| `(BoogieExpr| ( $x:BoogieExpr ) ) => do withRef x <| collectMutVars x
| `(BoogieExpr| $x:BoogieExpr * $y:BoogieExpr) => do
  let x <- withRef x <| collectMutVars x
  let y <- withRef y <| collectMutVars y
  return x.union y
| `(BoogieExpr| $x:BoogieExpr + $y:BoogieExpr) => do
  let x <- withRef x <| collectMutVars x
  let y <- withRef y <| collectMutVars y
  return x.union y
| `(BoogieExpr| $x:ident) => do
  let x := x.getId
  if (<- getThe BoogieElab).vars.contains x then return Std.HashSet.ofList [x]
  else throwError "collectMutVars: No such mutable variable {x}"
| _ => throwUnsupportedSyntax

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


/-- Evaluate a boogie expression, assuming that the Lean local context already contains variables
  which have been read from the boogie state monad, so assuming that we are within `withReadMutVars`. -/
private partial def elabBoogieExprPure (A : Q(Type)) : TSyntax `BoogieExpr -> BoogieElabM Q($A)
| `(BoogieExpr| $n:num ) => do
  let n : Nat := n.getNat
  if !(<- isDefEq A q(Int)) then throwError "elabBoogieExpr: type must be int for int literals"
  have ret : Q(Int) := q(Int.ofNat $n)
  return ret
| `(BoogieExpr| ( $x:BoogieExpr ) ) => do withRefQ x <| elabBoogieExprPure A x
| `(BoogieExpr| $x:BoogieExpr * $y:BoogieExpr) => do
  if !(<- isDefEq A q(Int)) then throwError "elabBoogieExpr: type must be Int"
  let x <- withRefQ x <| elabBoogieExprPure q(Int) x
  let y <- withRefQ y <| elabBoogieExprPure q(Int) y
  have : Expr := q($x * $y)
  return this
| `(BoogieExpr| $x:BoogieExpr + $y:BoogieExpr) => do
  if !(<- isDefEq A q(Int)) then throwError "elabBoogieExpr: type must be Int"
  let x <- withRefQ x <| elabBoogieExprPure q(Int) x
  let y <- withRefQ y <| elabBoogieExprPure q(Int) y
  have : Expr := q($x + $y)
  return this
| `(BoogieExpr| $x:BoogieExpr <= $y:BoogieExpr) => do
  if !(<- isDefEq A q(Bool)) then throwError "elabBoogieExpr: type must be Bool"
  let x <- withRefQ x <| elabBoogieExprPure q(Int) x
  let y <- withRefQ y <| elabBoogieExprPure q(Int) y
  have : Q(Bool) := q(($x <= $y : Bool))
  return this
| `(BoogieExpr| $x:ident) => do
  let some ldecl := (<- getLCtx).findFromUserName? x.getId | throwError "elabBoogieExpr: No such local var {x.getId}"
  if !(<- isDefEq ldecl.type q($A)) then throwError "elabBoogieExpr: Local var {x.getId} has type {ldecl.type} but is expected to have type {A}"
  return ldecl.toExpr
| _ => throwUnsupportedSyntax

#check 1

/-- Given a boogie expression `x + y`, produces an expression `bind (get "x") (fun x => bind (get "y") (fun y => pure (x + y))) : Boog Int`. -/
partial def elabBoogieExpr (A : Q(Type)) (stx : TSyntax `BoogieExpr) : BoogieElabM Q(Boog $A) := do
  let vars <- collectMutVars stx
  withReadMutVars vars.toList A (do
    let val : Q($A) <- elabBoogieExprPure A stx
    let m_val : Q(Boog $A) := q(Pure.pure $val)
    return m_val
  )

#check @WellFounded.fix (BoogieState) (fun _ => Boog Unit) ?r ?wf

/-
How do you write fixpoints for monads?
  R :    S             -> (S × A)    = St A
  R : (s:S) -> (s < _) -> (S × A)    = ??? A

Alternatively, the more classical fixpoint view:
           f                 : A -> M A
  fun a => f a               : A -> M A     "f"
  fun a => (f a) >>= f       : A -> M A     "f ∘ f"
  fun a => (f a) >>= f >>= f : A -> M A     "f ∘ f ∘ f"
And eventually we reach a point where f no longer changes its state, i.e.
  fun a => (f a) >>= f    =    fun a => (f a)
So we get something like:
  def HasFix [Monad M] (f : A -> M A) : Prop := ∃x, f x >>= f = f x
  `asdf`
But we care about potential nontermination...
! This doesn't seem worth it, just do ITrees or `Delay` at this point...
-/

-- noncomputable def Boog.fix (r : BoogieState -> BoogieState -> Prop) (wf : WellFounded r)
--   -- (body : (m' : Boog Unit) ×' r (m' s).2 s)
--   /- -/
--   (body : Boog Unit)
--   (body : (s : BoogieState) -> (R : (s' : BoogieState) -> r s' s -> BoogieState) -> BoogieState)
--   : Boog Unit
--   := fun s =>
--     pure <| @WellFounded.fix  _ (fun _ => _) r wf (fun s R => body) s

mutual
  partial def elabBoogieCommands (cmds : TSyntaxArray `BoogieCommand) : BoogieElabM Q(Boog Unit) := do
    cmds.foldlM (fun (acc : Q(Boog Unit)) (cmd : TSyntax _) => do
      let cmd : Q(Boog Unit) <- withRef cmd <| elabBoogieCommand cmd
      return q(Boog.seq $acc $cmd)
    ) q(Boog.skip)

  /-- Elaborates a command such as `x := 2 * y;` into a monadic action. -/
  partial def elabBoogieCommand : TSyntax `BoogieCommand -> BoogieElabM Q(Boog Unit)
  | _stx@`(BoogieCommand| $x:ident := $e:BoogieExpr; ) => do
    let val <- elabBoogieExpr q(Int) e
    let xStr : String := x.getId.toString
    let cmd : Q(Boog Unit) := q(Boog.set $xStr $val)
    -- Term.addTermInfo' stx cmd
    return cmd
  | `(BoogieCommand| if $cond { $t* } $[else { $e* }]?) => do
    let cond <- elabBoogieExpr q(Bool) cond
    let t <- elabBoogieCommands t
    if let some e := e then
      let e <- elabBoogieCommands e
      return q(Boog.ifthenelse $cond $t $e)
    else
      return q(Boog.ifthen     $cond $t   )
  | `(BoogieCommand| while $cond { $body* }) => do
    let _cond <- elabBoogieExpr q(Bool) cond
    let _body <- elabBoogieCommands body
    throwError "while loops not yet implemented"
  | _ => throwUnsupportedSyntax
end

def elabBoogieVarBinder : TSyntax `BoogieVarBinder -> BoogieElabM (Name × Q(Type))
| `(BoogieVarBinder| $id:ident : $type:BoogieType) => do
  let ty <- elabBoogieType type
  Term.addTermInfo' type ty
  return (id.getId, ty)
| _ => throwUnsupportedSyntax

/-- Elaborate a boogie procedure. You will usually pass a fresh metavar into `Ty`. Returns its name and body, also constrains the type `Ty`. -/
def elabBoogieProc : TSyntax `BoogieProc -> BoogieElabM (String × Q(Boog Unit))
| `(BoogieProc| procedure $proc ( $binders,* ) returns ($retBinder) { $body* }) => do
  let binders <- binders.getElems.mapM fun (b : TSyntax _) => withRef b <| do elabBoogieVarBinder b
  binders.forM fun (n, _ty) => declareVar n
  let (retVarName, _retVarType) <- withRef retBinder <| elabBoogieVarBinder retBinder
  declareVar retVarName
  return (proc.getId.toString, <- elabBoogieCommands body)
| _ => throwUnsupportedSyntax

def runBoogieElab' (m : BoogieElabM A) : TermElabM (A × BoogieElab) := StateT.run m { }

def runBoogieElab (m : BoogieElabM A) : TermElabM A := Prod.fst <$> runBoogieElab' m

end Elab

/-- Actually execute a boogie program. -/
def runBoogie (m : Boog Unit) : BoogieState :=
  let s₀ : BoogieState := { vars := {} }
  let ((), s') := StateT.run m s₀
  s'

elab stx:BoogieProc : command => do
  Command.liftTermElabM do
    runBoogieElab do
      let (name, body) <- elabBoogieProc stx
      let decl : DefinitionVal := {
        name := name.toName
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

set_option trace.auto.smt.printCommands true

/-
  (PUnit.unit, { vars := (state.vars.insert "x" (state.vars.getD "x" 0 + 1)).insert "x" (state.vars.getD "x" 0 + 1 + 2) })
= (PUnit.unit, { vars := (state.vars.insert "x" (state.vars.getD "x" 0 + 2)).insert "x" (state.vars.getD "x" 0 + 2 + 1) })
-/

namespace Example1
  procedure test1(x: int, y: int) returns (k: int) { x := x + 1; x := x + 2; }
  procedure test2(x: int, y: int) returns (k: int) { x := x + 2; x := x + 1; }

  example (state) : test1 state = test2 state := by
    rw [test1, test2]
    simp [Boog.skip, Boog.set, Boog.get, Boog.set, Boog.seq, bind_eq2
      StateT.get, StateT.set, getThe, modifyThe, StateT.modifyGet,
      instMonadStateOfMonadStateOf, instMonadStateOfStateTOfMonad]
    unfold StateT.get
    unfold StateT.modifyGet
    simp [pure, StateT.pure]
    simp [bind_eq2]
    simp [Std.HashMap.insert, Std.HashMap.getD]
    auto
    done

end Example1

-- def printContext {Γ : Context} (vars : denoteContext Γ) : String :=
--   Γ.Var.foldr (fun v acc => s!"{v} ↦ {vars v}, {acc}") ""

-- instance : Repr (denoteContext Γ) where reprPrec ctx _ := printContext ctx
