import Lean
import Std
import Qq
import ITree
import LeanBoogie.Effect.AssumeAssert
import LeanBoogie.Effect.Mem
import LeanBoogie.State
import LeanBoogie.TraceClasses
import Batteries.Data.Array.Monadic

namespace LeanBoogie
open Lean Elab Term Meta Qq
open Std (HashSet HashMap)
open ITree

section Util
  local instance [BEq A] [Hashable A] [ToString A] : ToString (Std.HashSet A) where
    toString set := set.toList.toString

  /-- Small convenience type. Often we want to store the source `Syntax` for a `Name` to be able
    to throw an error using `throwErrorAt stx`. -/
  structure NameWithStx where
    stx : TSyntax `ident
  deriving Inhabited, Repr
  abbrev NameWithStx.getId : NameWithStx -> Name := fun ⟨stx⟩ => stx.getId
  -- instance : Coe (TSyntax `ident) NameWithStx where coe x := ⟨x⟩
  instance : Coe NameWithStx (TSyntax `ident) where coe x := x.stx
  instance : Coe NameWithStx Syntax where coe x := x.stx
  instance : Coe NameWithStx Name where coe x := x.stx.getId
  instance : BEq NameWithStx where beq a b := a.1.getId == b.1.getId
  instance : Hashable NameWithStx where hash n := hash n.1.getId
  instance : ToString NameWithStx where toString n := toString n.1.getId

  /-- Adapter to turn `List (ITree ...)` into `Fin N -> ITree ...`, which is what `iter` expects. -/
def selectBlock {E : Type -> Type} {N : Nat} (blocks : List (ITree E (Fin N ⊕ Unit))) (h : blocks.length = N)
  (i : Fin N) : ITree E (Fin N ⊕ Unit)
  := blocks.get (h.symm ▸ i)

end Util

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
  syntax ident noWs "(" BoogieExpr,* ")" : BoogieExpr -- boogie non-effectful function call
  syntax ident : BoogieExpr -- variable
  syntax num : BoogieExpr -- literal
  -- syntax num (noWs "bv" noWs num)? : term -- BitVec literal, e.g. `10bv32`
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
  syntax "goto " ident,* "; " : BoogieGoto
  declare_syntax_cat BoogieReturn
  syntax "return" "; " : BoogieReturn
  syntax BoogieBlockGotoOrReturn := BoogieGoto <|> BoogieReturn

  declare_syntax_cat BoogieCommand
  syntax ident " := " BoogieExpr "; " : BoogieCommand
  syntax "if " BoogieExpr " { " BoogieCommand* " }" ("else" " { " BoogieCommand* " }")? : BoogieCommand
  syntax "while " BoogieExpr " { " BoogieCommand* " }" : BoogieCommand
  syntax "call " BoogieIdent "(" BoogieExpr,* ")" "; " : BoogieCommand
  syntax BoogieAssume : BoogieCommand

  declare_syntax_cat BoogieBlock
  syntax ident ": " BoogieAssume* BoogieCommand* BoogieBlockGotoOrReturn : BoogieBlock

  declare_syntax_cat BoogieVarCmd
  syntax "var " BoogieVarBinder "; " : BoogieVarCmd

  declare_syntax_cat BoogieProc
  syntax "procedure " ident "(" BoogieVarBinder,* ")"
    (" returns " "(" BoogieVarBinder ")")?
    " { "
      BoogieVarCmd*
      BoogieCommand* -- these "blockless" commands will get wrapped into a block of their own, if there are any subsequent blocks
      (BoogieBlockGotoOrReturn)?
      BoogieBlock*
    " }" : BoogieProc
end Syntax






section Elab
variable {E : Q(Type -> Type)}

/-
  ## Elaboration
  Takes `Lean.Syntax` (or, well, `Lean.TSyntax`) and produces `Lean.Expr`.
  You'll often see for example `Q(Nat)` instead of `Lean.Expr`, but they are the same! The `Q` is
  a convenience macro from the Quote4 library, which allows you to annotate `Lean.Expr` with their
  type. This is not a formal proof, it is roughly equivalent to a linter.

  The elaboration code effectively increases the trusted code amount, so should be kept simple.

  ### What kind of `Lean.Expr` should we produce?
  - An `ITree`, which is a shallow embedding.
  - Some deep embedding.

  ### Blocky, unstructured programs
  Let's say you have two blocks:
  ```
  A: assume α; a;
  B: assume β; b;
  ```
  In general, Boogie `goto A, B;` statements are non-deterministic.
  Boogie translates even deterministic jumps (e.g. originating from `if _ then _ else _`) into
  non-deterministic gotos.
  You have the following options when encountering `goto A, B;`:
  1. Try to prove that `(¬α) <-> β`, therefore we have found a deterministic jump which can be
     translated using an `if`. This is not always the case, however. It also increases the size
     of the DSL, increasing the trusted code amount.
  2. *Ideally:* Use the `Choice` effect to non-deterministically choose between `A` and `B` branches,
     and then use the `AssumeAssert` effect for `α` and `β`.
  3. None of the above, instead adopting a hacky strategy:
     Go to the first label for which we can synthesize `Decidable α` for its leading `assume α;`,
     and it decides to true. If no blocks match, we `spin`.
     We currently use this approach.
     This approach does not faithfully model Boogie semantics, and we should move away from it.

  ### Obtaining executable code
  When you do use `AssumeAssert` and `Choice` (See (2) in the previous section), you may want to obtain
  executable code. For `AssumeAssert` this is easy: You simply provide a proof via an axiom, e.g. `sorry`.
  For `Choice` this is not as straightforward. However, often programs are only non-deterministic on
  the surface, and the leading assumes for each block are disjoint, in which case we would still
  like to avoid forking the entire program state.
-/


/-- An elaborated Boogie block.

  Ideally we would only store `code : Q(ITree $E (Fin ?NBlocks ⊕ Unit))`. However, currently we
  - Store `assumes` since our DSL currently uses a hack making Boogie `goto ..;` deterministic.
    This can be avoided by using `AssumeAssert` and `Choice` effects instead.

  - Store `gotos` because when one block gets elaborated individually, we don't know yet how many
    blocks there are and what their indices are.
    This can be avoided by adding `N : Q(Nat)` as parameter and
    `blockIndices : HashMap Name Q(Fin $N)` as field to `BoogieElab`, and using metavariables
    to postpone finding concrete values there. We can then backfill those values by assigning
    the metavariables.
-/
structure EBlock (E : Q(Type -> Type)) /- (NBlocks : Q(Nat)) -/ where
  label : NameWithStx
  /-- Any leading assumes for this block. With `Decidable` already synthesized for it,
    hence why it returns `Bool` and not `Prop`. -/
  assumes : Q(ITree $E Bool)
  /-- Code without `assume`s and without `goto`s. -/
  code : Q(ITree $E Unit)
  /-- The labels from `goto A, B, C;`. Empty list `[]` for `return;`. -/
  gotos : Array NameWithStx
deriving Inhabited, Repr

/-- Elaborated Boogie procedure. Notably absent: local variables. -/
structure EBoogieProc where
  name : Name
  /-- Global effects, for example global variables, `AssumeAssert`, `Choice`, etc. -/
  E : Q(Type -> Type)
  /-- Parameters -/
  P : Q(Con)
  /-- Return type. -/
  R : Q(Ty)
  code : Q($P -> ITree $E $R)

/-- An elaborated variable. Stores events which allow reading or writing the variable, not
  the variable name or index directly. The effect parameter `E` may be something complicated
  such as `Mem Γ & AssumeAssert & Mem Δ`, in which case `read` will be for example
  `EffProd.left (EffProd.left (EffProd.right (Mem.rd ...)))`, "navigating" through `E`. -/
structure EVar (E : Q(Type -> Type)) where
  /-- The type of this variable. -/
  A : Q(Ty)
  /-- An event which reads the variable. -/
  read : Q($E $A)
  /-- An event which allows you to write this variable. -/
  write : Q($A -> $E Unit)
  deriving Repr

/-- Mapping from variable name to its `read` and `write`. This is relative to `E`. -/
abbrev VarInfo (E : Q(Type -> Type)) : Type := Std.HashMap Name (EVar E)

def VarInfo.inl {F : Q(Type -> Type)} (vi : VarInfo E) : VarInfo q($E & $F) :=
  vi.fold (fun acc n vi => acc.insert n {
    A := vi.A
    read := q(.left $vi.read)
    write := q(fun x => .left ($vi.write x))
  }) { }

def VarInfo.inr {F : Q(Type -> Type)} (vi : VarInfo E) : VarInfo q($F & $E) :=
  vi.fold (fun acc n vi => acc.insert n {
    A := vi.A
    read := q(.right $vi.read)
    write := q(fun x => .right ($vi.write x))
  }) { }

def VarInfo.merge (v₁ v₂ : VarInfo E) : VarInfo E := v₁.insertMany v₂

/-- Knowledge about the boogie program while elaborating the boogie syntax.
  You could remember all kinds of analysis in this monad. -/
structure BoogieElab (E : Q(Type -> Type)) where
  procName : Name
  /-- Mapping of names to de-Brujin indices, but also the type of the variable. -/
  varInfo : VarInfo E
  -- nBlocks : Q(Nat)
  -- blockIndices : Std.HashMap Name Q(Fin $nBlocks) := {}
deriving Inhabited

abbrev BoogieElabM (E : Q(Type -> Type)) := StateT (BoogieElab E) TermElabM


def lookupVar (varName : Name) : BoogieElabM E (Option (EVar E)) := do
  let res := (<- get).varInfo.get? varName
  return res

/-- If we are elaborating `procedure myproc(...) ... { ... }`, return `procName`.  -/
def getProcName : BoogieElabM Γ Name := do return (<- get).procName

/-- Create a name in a namespace within our current boogie proc. -/
def mkNameWithPrefix (n : Name) : BoogieElabM Γ Name := do
  return (<- getCurrNamespace) ++ (<- getProcName) ++ n


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
  -- but we do collect variables in arguments
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

/-- Read mutable variables from the boogie state monad, introducing them into the local context, and then run `m` in this new local context.
  Returns an expression like:
  ```
  bind (read "x") fun x =>
    bind (read "y") fun y =>
      /- whatever m evaluates to -/
  ``` -/
def withReadMutVars (vs : List NameWithStx) (X : Q(Type)) (m : BoogieElabM E Q(ITree $E $X)) : BoogieElabM E Q(ITree $E $X) := do
  match vs with
  | [] => m
  | v :: vs =>
    if let some { A, read, .. } := <- lookupVar v then
      let a : Q(ITree $E $A) := q(trigger $read) -- no `embed` here! ==> Less clutter
      let b : Q($A -> ITree $E $X) <- withLocalDeclDQ v.getId q($A) fun (v : Q($A)) => do
        let e : Q(ITree $E $X) <- withReadMutVars vs X m
        mkLambdaFVars #[v] e
      return q($a >>= $b)
    else
      throwErrorAt v "withReadMutVars: Unknown variable"

mutual
  partial def elabBoogieExprPure' (stx : TSyntax `BoogieExpr) : BoogieElabM E ((A : Q(Type)) × Q($A)) := do
    let A <- mkFreshExprMVarQ q(Type)
    let e <- elabBoogieExprPure A stx
    return ⟨A, e⟩

  partial def elabBinOpInst (A : Q(Type)) (x y : TSyntax `BoogieExpr)
    (Inst : (X Y : Q(Type)) -> Q(Type))
    (f : {X Y : Q(Type)} -> {_inst : Q($(Inst X Y))} -> (x : Q($X)) -> (y : Q($Y)) -> BoogieElabM E Q($A))
    : BoogieElabM E Q($A)
    := do
    let ⟨X, x⟩ <- elabBoogieExprPure' x
    let ⟨Y, y⟩ <- elabBoogieExprPure' y
    let inst <- mkInstMVar (Inst X Y)
    @f X Y inst x y

  /-- Evaluate a boogie expression, assuming that the Lean local context already contains variables
    which have been read from the boogie state monad, so assuming that we are within `withReadMutVars`. -/
  private partial def elabBoogieExprPure (A : Q(Type)) (stx : TSyntax `BoogieExpr) : BoogieElabM E Q($A) := do
    withTraceNode `LeanBoogie.dsl (logger m!"elabBoogieExprPure (A≡{A}) `{stx}`") do
      let ret <- withRef stx (go stx)
      let retTy <- inferType ret
      if !(<- isDefEq retTy A) then throwError "Expected {A} but got {retTy}"
      Term.addTermInfo' stx ret
      let ret <- instantiateExprMVars ret
      return ret
  where go
  | `(BoogieExpr| $n:num ) => do
    let n <- Term.elabNumLit n q($A)
    return n
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
  partial def elabBoogieExpr (A : Q(Type)) (stx : TSyntax `BoogieExpr) : BoogieElabM E Q(ITree $E $A) := do
    withTraceNode `LeanBoogie.dsl (logger m!"elabBoogieExpr `{stx}`") do
      let vars <- collectMutVars stx
      withReadMutVars vars.toList A (do
        let val : Q($A) <- elabBoogieExprPure A stx
        let m_val : Q(ITree $E $A) := q(Pure.pure $val)
        return m_val
      )
end

partial def elabBoogieFormula (stx : TSyntax `BoogieFormula) : BoogieElabM E Q(Prop) := do
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

-- partial def elabBoogieAssume : TSyntax `BoogieAssume -> BoogieElabM E Q(ITree $E Unit)
-- | stx@`(BoogieAssume| assume%$tok_assume $φ:BoogieFormula; ) => do
--   withTraceNode `LeanBoogie.dsl (logger m!"elabBoogieAssume `{stx}`") do
--     let vars <- collectMutVarsFormula φ
--     withReadMutVars vars.toList q(Unit) do
--       let φ : Q(Prop) <- elabBoogieFormula φ
--       let ret : Q(ITree $E Unit) := q(LeanBoogie.assume $φ)
--       Term.addTermInfo' stx ret
--       Term.addTermInfo' tok_assume (ret.getBoundedAppFn 0)
--       return ret
-- | stx => throwError "elabBoogieAssume: Unknown syntax {stx}"

/-- Creates a program which decides the truth value of each assume, returns conjunction of that. -/
partial def elabBoogieAssume' : TSyntax `BoogieAssume -> BoogieElabM E Q(ITree $E Bool)
| stx@`(BoogieAssume| assume $φ:BoogieFormula; ) => withRef stx do
  withTraceNode `LeanBoogie.dsl (logger m!"elabBoogieAssume' `{stx}`") do
    let vars <- collectMutVarsFormula φ
    withReadMutVars vars.toList q(Bool) do
      let φ : Q(Prop) <- elabBoogieFormula φ
      let dφ <- synthInstanceQ q(Decidable $φ) -- ! Need `Decidable`, or later: Use events
      let ret : Q(ITree $E Bool) := q(return @decide $φ $dφ)
      return ret
| stx => throwError "elabBoogieAssume: Unknown syntax {stx}"

-- This is not in `BoogieElabM` because at this point we don't know the variables (and thus Γ) yet.
def elabBoogieVarBinder : TSyntax `BoogieVarBinder -> TermElabM (TSyntax `ident × Ty)
| stx@`(BoogieVarBinder| $id:ident : $type:BoogieType) => withRef stx do
  let ty : Ty <- elabBoogieType type
  Term.addTermInfo' type (<- whnf q(TyA $ty))
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
  partial def elabBoogieCommand (stx : TSyntax `BoogieCommand) : BoogieElabM E Q(ITree $E Unit) := do
    withTraceNode `LeanBoogie.dsl (logger m!"elabBoogieCommand `{stx}`") do
      withRef stx do
        withSynthesize do
          let ret <- go stx
          let ret <- instantiateExprMVarsQ ret
          Term.addTermInfo' stx ret
          return ret
  where go
  | `(BoogieCommand| $vName:ident := $e:BoogieExpr; ) => do
    if let some { A, write, .. } := <- lookupVar vName.getId then -- `Mem.wr v` : Int -> (Mem) Unit
      let val : Q(ITree $E $A) <- elabBoogieExpr q($A) e
      -- Term.addTermInfo' vName q($vq)
      let cmd : Q(ITree $E Unit) := q($val >>= fun val => trigger ($write val))
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

  partial def elabBoogieCommands (cmds : TSyntaxArray `BoogieCommand) : BoogieElabM E Q(ITree $E Unit) := do
    cmds.foldlM (fun (acc : Q(ITree $E Unit)) (cmd : TSyntax _) => do
      let cmd : Q(ITree $E Unit) <- withRef cmd <| elabBoogieCommand cmd
      return q(do ($acc); ($cmd))
    ) q(return ())
end

/-- Elaborate a block, for unstructured programs.
  This uses a hack to synthesize `Decidable` for the leading assumes.
  Long-term, we want to use `AssumeAssert` and `Choice` instead.  -/
def elabBoogieBlock : TSyntax `BoogieBlock -> BoogieElabM E (EBlock E)
| stx@`(BoogieBlock| $lbl:ident : $assumes:BoogieAssume* $cmds:BoogieCommand* $gotoOrReturn:BoogieBlockGotoOrReturn ) => do
  withTraceNode `LeanBoogie.dsl (logger' m!"elabBoogieBlock `{stx}`") do
    let lbl := lbl
    let assumes : Array Q(ITree $E Bool) <- assumes.mapM elabBoogieAssume'
    let assumes : Q(ITree $E Bool) :=
      -- We do this extra check to avoid putting `q(return true)` as the neutral element in the fold
      /- Side remark: These sort of handy little optimizations seem innocent, but they increase the
        amount of trusted code.  -/
      if h : assumes.size = 0 then q(return true)
      else assumes[1:].toArray.foldl (fun (acc a : Q(ITree $E Bool)) =>
        q(do
          let acc <- ($acc)
          let a <- ($a)
          return acc && a
        ))
        assumes[0]
    let cmds : Q(ITree $E Unit) <- elabBoogieCommands cmds
    match gotoOrReturn with
    | `(BoogieBlockGotoOrReturn| goto $gotos,*;) =>
      -- let gotos : Array Name := gotos.getElems.map (fun g => g.getId)
      return ⟨⟨lbl⟩, assumes, cmds, gotos.getElems.map (⟨.⟩)⟩
    | `(BoogieBlockGotoOrReturn| return;) =>
      return ⟨⟨lbl⟩, assumes, cmds, #[]⟩
    | _ => throwError "elabBoogieBlock: Unknown syntax {gotoOrReturn}"
| stx => throwError "elabBoogieBlock: Unknown syntax {stx}"

/-- Takes a bunch of pre-elaborated individual blocks, and ties them together with `iter`.

  If there are multiple goto labels `goto A, B, C;`, uses a choice effect to non-deterministically
  go to all labels simultaneously, and then uses an `assume` effect in each branch. -/
def wireUpBlocks (blocks : Array (EBlock E)) : BoogieElabM E Q(ITree $E Unit) := sorry


private def liftToDef {T : Q(Type)} (name : Name) (t : Q($T)) : MetaM Q($T) := do
  let t <- instantiateExprMVarsQ t
  let decl : DefinitionVal := {
    name
    levelParams := []
    type := <- inferType t
    value := t
    hints := .abbrev
    safety := .safe
  }
  addDecl (.defnDecl decl)
  return .const name []

private def liftBlockToDef {N : Nat} (name : Name) (block : Q(ITree $E (Fin $N ⊕ Unit))) : MetaM Q(ITree $E (Fin $N ⊕ Unit)) := do
  liftToDef name block

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
def wireUpBlocksDeterministic {E} (blocks : List (EBlock E)) (blocks_h : ¬blocks.length = 0)
  : BoogieElabM E Q(ITree $E Unit)
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
  let buildBlock (block : EBlock E) : BoogieElabM E Q(ITree $E (Fin $N ⊕ Unit)) := do
    if block.gotos.isEmpty then
      -- `goto;` means `return;`, don't spin in that case
      return q(do ($block.code); return .inr ())
    else
      let decideBranch : Q(ITree $E (Fin $N ⊕ Unit)) <- block.gotos.foldrM
        (fun (gotoLabel : NameWithStx) acc => do
          let some (gotoIdx : Fin N) := blockIndices.get? gotoLabel.getId
            | throwErrorAt gotoLabel "Unknown block label"
          return q(do if <- $(blocks[gotoIdx].assumes) then return .inl ($gotoIdx) else ($acc))
        )
        q(spin) -- we could get rid of this `spin` if we can prove that always at least one of the assumes is true.
      return q(do ($block.code); ($decideBranch))

  let ns := (<- getCurrNamespace) ++ (<- getProcName)
  let blocks' : List Q(ITree $E (Fin $N ⊕ Unit)) <- blocks.mapM fun b => do
    let block <- buildBlock b
    liftBlockToDef (ns ++ b.label.getId) block
  have : blocks'.length = blocks.length := by sorry
  let ⟨blocks'', h⟩ := List.q_len N blocks' (this ▸ hN)
  let prf <- assumeQ q(0 < $N) -- this can be optimized
  return q(Iter.iter (selectBlock (N := $N) $(blocks'') $h) ⟨0, $prf⟩)


/-- Add a `Mem Γ` to the effect stack.
  Inside `m`, `varInfo` has been updated to produce the correct event of type `E & Mem Γ`, using
  either `EffProd.left` or `EffProd.right`.

  `Γ` is also passed pre-quoted as `Γq` in order to allow the constructed expressions to refer
  to contexts lifted to definitions, for example. -/
def withVars (Γ : Con) (Γq : Q(Con)) (Γ_names : List NameWithStx) (m : BoogieElabM q($E & Mem $Γq) A) : BoogieElabM E A := do
  let vi_left := (<- get).varInfo.inl
  let Γ_varInfo <- buildVarInfo Γ Γq Γ_names
  let vi_right := Γ_varInfo.inr -- our new vars. maps `Mem.rd` to `EffProd.right Mem.rd`
  let st := {
    procName := <- getProcName
    varInfo := VarInfo.merge vi_right vi_left
  }
  (StateT.run' m st : TermElabM A)
where
  buildVarInfo (Γ : Con) (Γq : Q(Con)) (names : List NameWithStx) : TermElabM (VarInfo q(Mem $Γq)) := do
    let mut varInfo : Std.HashMap Name (EVar q(Mem $Γq)) := {}
    for h : (i : Nat) in [0 : Γ.length] do -- surely this can be written nicer somehow?
      have h : i < Γ.length := by simp_all only [Membership.mem, zero_le, Array.toList_eq, Array.append_data, List.append_assoc, List.map_append, List.length_append, List.length_map, Array.data_length, true_and]
      let idx : Fin Γ.length := ⟨i, h⟩
      let idxq : Q(Fin ($Γq).length) := (q($idx) : Expr)
      let A : Ty := Γ[idx]
      let vq : Q(Var $Γq $A) := (q(@Var.ofIdx $Γq $idxq) : Expr)
      varInfo <- varInfo.insertNewOrFail names[i]!.getId
        {
          A := q($A)
          read := q(Mem.rd $vq)
          write := q(Mem.wr $vq)
        }
        (@fun a => throwErrorAt names[i]! "Duplicate variable name {a} in {names}")
    return varInfo

def runBoogieElab (procName : Name) (m : BoogieElabM q(None) X) : TermElabM X := do
  let st : BoogieElab q(None) := { procName, varInfo := {} }
  StateT.run' m st

/-- Elab all arg, ret, and var binders, bundling them up into a `Γ : Con`. Also builds mapping
  from variable names to variable indices which is stored inside `BoogieElabM`. -/
def elabProcContext (stx : TSyntax `BoogieProc)
  (cont : (F : Q(Type -> Type)) ->
    (cmds : TSyntaxArray `BoogieCommand) ->
    (blocks : TSyntaxArray `BoogieBlock) ->
    (gotoOrReturn : Option <| TSyntax `LeanBoogie.BoogieBlockGotoOrReturn) ->
    -- BoogieElabM q($E & $F) Q(ITree ($E & $F) Unit)
    BoogieElabM F Q(ITree $F Unit)
  )
  : TermElabM EBoogieProc := do
  match stx with
  | `(BoogieProc| procedure $proc ( $argBinders,* ) $[returns ($retBinder)]? { $varBinders:BoogieVarCmd* $cmds:BoogieCommand* $[$gotoOrReturn:BoogieBlockGotoOrReturn]? $blocks:BoogieBlock* }) => do
    let argBinders <- argBinders.getElems.mapM (fun b => liftM (elabBoogieVarBinder b))
    let retBinder <- retBinder.mapM (fun b => liftM (elabBoogieVarBinder b))
    let varBinders <- elabBoogieVarCmds varBinders

    runBoogieElab proc.getId do
      let E : Q(Type -> Type) := q(None) -- Eventually we want E to be customizable, with e.g. global variables, Assume/assert, etc
      -- let hE : Q(Handler $E (ITree $E)) := q(Handler.none)
      let P : Con := argBinders.map Prod.snd |>.toList
      let Pq : Q(Con) <- liftToDef (<- mkNameWithPrefix `P) q($P)
      let R : Option Ty := retBinder.map Prod.snd
      let L : Con := varBinders.map Prod.snd |>.toList
      let Lq : Q(Con) <- liftToDef (<- mkNameWithPrefix `L) q($L)

      let P_names : List NameWithStx := argBinders.map (.mk ∘ Prod.fst) |>.toList
      let R_names : List NameWithStx := retBinder.map (.mk ∘ Prod.fst) |>.toList
      let L_names : List NameWithStx := varBinders.map (.mk ∘ Prod.fst) |>.toList

      withVars P Pq P_names do
        if let some R := R then
          withVars [R] q([$R]) R_names do
            withVars L Lq L_names do
              let code : Q(       ITree ($E & Mem $Pq & Mem [$R] & Mem $Lq)    Unit) <- cont _ cmds blocks gotoOrReturn
              let code := q(interp (State.handler3 (M := ITree $E) $Pq [$R] $Lq Handler.none) $code default default)
              let code : Q($Pq -> ITree $E $R) := q(fun p => (Prod.fst ∘ Prod.snd ∘ Prod.fst) <$> $code p) -- `Prod.snd ∘ Prod.fst` gives you `ConA [$R]`, and then `Prod.fst ∘ Prod.snd ∘ Prod.fst` gives you `TyA $R`
              -- let code : Q($Pq -> ITree $E $R) := q(fun p => do let res <- ($code) p; return res.fst.snd.fst)
              return { name := <- getProcName, E, P := Pq, R := q($R), code }
        else
          withVars L Lq L_names do
            let code : Q(ITree ($E & Mem $Pq & Mem $Lq)  Unit      ) <- cont _ cmds blocks gotoOrReturn
            let code : Q(ITree ($E & Mem $Pq          ) (Unit × $Lq)) := q(State.run $code (default : $Lq))
            let code : Q($Pq -> ITree $E ((Unit × $Lq) × $Pq)) := q(State.run $code)
            let code : Q($Pq -> ITree $E   Unit            ) := q(fun p => do let _res <- ($code) p; return ())
            return { name := <- getProcName, E, P := Pq, R := q(.unit), code }
  | stx => throwError "elabBoogieProcFrame: Unknown syntax {stx}"

def elabGotoOrReturn (stx : TSyntax `LeanBoogie.BoogieBlockGotoOrReturn) : TermElabM (Array NameWithStx) := do
  match stx with
  | `(BoogieBlockGotoOrReturn| goto $gotos,*;) => return gotos.getElems.map (⟨.⟩);
  | `(BoogieBlockGotoOrReturn| return;) => return #[]
  | _ => throwUnsupportedSyntax

def elabBoogieProc (stx : TSyntax `BoogieProc) : TermElabM EBoogieProc := do
  elabProcContext stx fun (E : Q(Type -> Type)) cmds blocks gotoOrReturn => do
    if h : blocks.size = 0 then
      -- No labels declared at all, in that case we don't need to set up blocky stuff at all.
      elabBoogieCommands cmds
    else
      let blocks <- blocks.mapM elabBoogieBlock
      let gotos : Array NameWithStx <- do
        if let some g := gotoOrReturn then elabGotoOrReturn g
        else pure #[(blocks[0]'sorry).label] -- sorry := h
      let leadingBlock : Array (EBlock E) <- do
        if ¬ cmds.isEmpty then
          pure #[{
            label := ⟨<- `(ident| _leadingBlock)⟩
            assumes := q(return true)
            code := <- elabBoogieCommands cmds
            gotos := gotos
            : EBlock E
          }]
        else pure #[]
      let blocks := leadingBlock ++ blocks
      wireUpBlocksDeterministic blocks.toList sorry


open Lean Qq Meta in
simproc↓ nextBlock (Iter.iter (@selectBlock _ _ _ _) _) := fun e => do
  let_expr Iter.iter _ _ _ _ sb i := e | throwError "nextBlock: bug"
  let_expr selectBlock E N _blocks _hN := sb | throwError "nextBlock: bug"
  have E : Q(Type -> Type) := E
  have e : Q(ITree $E Unit) := e
  have N : Q(Nat) := N
  have i : Q(Fin $N) := i
  if i.isFVar then return .continue -- only simplify when we have a concrete block index, as opposed to an fvar such as `a`
  -- `A ≡ Fin $N`, `B ≡ Unit`, `M ≡ ITree $E`
  let rhs <- mkFreshExprMVarQ q(ITree $E Unit)

  -- transform `iter (selectBlock _ _) i` into e.g. `bbᵢ >>= ...`
  -- This is a little hacky since `rhs` is just an mvar and later we assign `rhs := e'`.
  let prf <- mkFreshExprMVarQ q($e = $rhs)
  let ([mvar], _) <- Elab.runTactic prf.mvarId! (<- `(tactic|
      rewrite [iter_fp', selectBlock];
      -- Since we have no simprocs for `List.getElem` (yet?), only for `Array.getElem`, we need to go
      -- via `List.get` since otherwise we get a timeout when simping `List.getElem`.
      simp only [List.get]
    )) | throwError "nextBlock: bug3"

  let_expr Eq _ e' _ := <- mvar.getType | throwError "nextBlock: bug4"
  have e' : Q(ITree $E Unit) := e'
  assertDefEq "nextBlock" e' rhs
  assertDefEq "nextBlock" (.mvar mvar) q(@Eq.refl (ITree $E Unit) $e')
  mvar.assign q(@Eq.refl (ITree $E Unit) $e') -- this shouldn't be required due to the isDefEq just above, but it is?

  -- unfold `bbᵢ`
  let_expr Bind.bind b1 b2 b3 b4 bb b5 := e' | throwError "nextBlock: bug6, have e' = {e'}"
  let Expr.const name .. := bb | throwError "nextBlock: bug7, have bb ≡ {bb}"
  let { expr := bb', .. } <- Meta.unfold bb name
  let e'' <- mkAppOptM ``Bind.bind #[b1, b2, b3, b4, bb', b5]
  return .visit {
    expr := <- instantiateExprMVars e''
    proof? := <- instantiateExprMVars prf -- don't need to use `bb'.proof?`, because works by defeq (delta-equiv)
  }


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
    let { name, code, .. } <- elabBoogieProc stx
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
    addDecl (.defnDecl decl)

namespace Test
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

procedure sum(n: int) returns (s: int) {
  var i: int;
  i := 0;
  s := 0;
  while (i <= n) {
    i := i + 1;
    s := s + i;
  }
}

#print sum
end Test

end Elab
