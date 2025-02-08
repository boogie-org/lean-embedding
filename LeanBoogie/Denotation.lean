import Lean
import ITree
import LeanBoogie.ConTy
import LeanBoogie.State
import LeanBoogie.Syntax
import LeanBoogie.Effect.AssumeAssert
import LeanBoogie.Effect.Choice
import LeanBoogie.Effect.Mem

open ITree
open LeanBoogie
namespace LeanBoogie

-- Syntax-free definitions

def goto : List (Fin b) -> ITree Choice (Fin b ⊕ Unit)
| [] => (.ret (.inr ())) -- Shouldn't actually happen
| [l] => (.ret (.inl l))
| ls => do
   let li <- choice (Fin ls.length)
   .ret (.inl (ls.get li))

-- Conditional goto, for deterministic programs
def cgoto : Bool -> Fin b -> Fin b -> ITree E (Fin b ⊕ Unit)
| c, t, e => if c then (.ret (.inl t)) else (.ret (.inl e))

class ToITree (α : Type) (E : Type -> Type) (R : Type) where
  toITree : α -> ITree E R

-- TODO: don't need separate constructors?
def denoteLiteral : Literal A -> TyA A
| .intL n => n
| .boolL b => b
| .bvL bv => bv
| .realL r => r

def denoteUnaryOp : UnaryOp A -> TyA A -> TyA A
| .notB, b => ¬b
| .negI, n => -n

--noncomputable
def denoteBinaryOp : BinaryOp A -> TyA A -> TyA A -> TyA A
| .addI, x, y => x + y
| .subI, x, y => x - y
| .mulI, x, y => x * y
| .divI, x, y => x / y -- TODO: double-check semantics
| .modI, x, y => x % y -- TODO: double-check semantics
--| .addR, x, y => x + y
--| .subR, x, y => x - y
--| .mulR, x, y => x * y
--| .divR, x, y => x / y -- TODO: double-check semantics
| .imp, a, b => a → b
| .and, a, b => a ∧ b
| .or, a, b => a ∨ b
| .equiv, a, b => a = b

def denoteRelationOp : (BEq (TyA A)) -> RelationOp A -> TyA A -> TyA A -> Bool
| _, .eq, a, b    => a == b
| _, .neq, a, b   => a != b
| _, .lessI, x, y => x < y

def denoteAppliable : Appliable A B -> TyA A -> TyA B
| .binop op    => denoteBinaryOp op
| .unop op     => denoteUnaryOp op
| .relop eq op => denoteRelationOp eq op
| .mapSelect   => id

def denoteExpr : ConA Γ -> Expr Γ A -> TyA A
| _, .lit l          => denoteLiteral l
| γ, .apply a e      => (denoteAppliable a) (denoteExpr γ e)
| γ, .applyExpr fe e => (denoteExpr γ fe) (denoteExpr γ e)
| γ, .var x          => ConA.get γ x
| γ, .lambda e       => λ x => denoteExpr (x, γ) e

-- Within an ITree, we don't need to pass around a context, and can just
-- use Mem.readAll.
def denoteExprI {A : Ty} {Γ : Con} (e: Expr Γ A) : ITree (Mem Γ) (TyA A) := do
  let γ <- Mem.readAll
  return (denoteExpr γ e)

def denoteFormula : ConA Γ -> Formula Γ -> Prop
| γ, .forallF p => forall x, denoteFormula (x, γ) p
| γ, .existsF p => exists x, denoteFormula (x, γ) p
| γ, .andF p q  => denoteFormula γ p /\ denoteFormula γ q
| γ, .orF p q  => denoteFormula γ p \/ denoteFormula γ q
| γ, .impF p q  => denoteFormula γ p -> denoteFormula γ q
| γ, .eqF p q   => denoteFormula γ p = denoteFormula γ q
| γ, .eqE e1 e2   => denoteExpr γ e1 = denoteExpr γ e2
| _, .litF b    => b
| γ, .boolF e   => denoteExpr γ e

def denotePropExprI (p: Formula Γ) : ITree (Mem Γ) Prop := do
  let γ <- Mem.readAll
  .pure (denoteFormula γ p)

instance exprITree : ToITree (Expr Γ A) (Mem Γ) (TyA A) where
  toITree := denoteExprI

def denotePassiveCommand : PassiveCommand Γ -> ITree (Mem Γ & AmAt) Unit
| .assert e => do assert (<- denotePropExprI e)
| .assume e => do assume (<- denotePropExprI e)

def denoteCommand : Command Γ -> ITree (Mem Γ & AmAt & E) Unit
| .passive p => denotePassiveCommand p
| .assign x e => do Mem.write x (<- denoteExprI e)

def denoteTransferCommand : (c: TransferCommand b Γ) -> ITree (Mem Γ & AmAt & Choice) (Fin b ⊕ Unit)
| .goto ls => goto ls
| .ret => .ret (.inr ())

def denoteBlock (blk: Block (Command Γ) Unit b Γ) : ITree (Mem Γ & AmAt & Choice) (Fin b ⊕ Unit) := do
  forM blk.simpleCmds denoteCommand
  denoteTransferCommand blk.transferCmd

def denoteBlocks (bs: Fin b -> Block (Command Γ) Unit b Γ) (b0: Fin b) : ITree (Mem Γ & AmAt & Choice) Unit :=
  Iter.iter (λ bi => denoteBlock (bs bi)) b0

def WhileEarly [Iter M] (c : M Bool) (body : M (Fin b ⊕ Unit)) : M (Fin b ⊕ Unit) :=
  iter (fun () => do
    if (<- c) then
      match (<- body) with
      | .inl b => return .inr (.inl b)
      | .inr _ => return .inl ()
    else
      return .inr (.inr ())
  )
  ()

mutual
def denoteStructuredCommand : StructuredCommand b Γ -> ITree (Mem Γ & AmAt & Choice) (Fin b ⊕ Unit)
| .ite c t e =>
  do if (<- denoteExprI c)
     then denoteStructuredCommands t
     else denoteStructuredCommands e
| .while c b => WhileEarly (denoteExprI c) (denoteStructuredCommands b)
| .cmd c => do denoteCommand c ; .pure (.inr ())
| .transfer t => denoteTransferCommand t

def denoteStructuredCommands :
  List (StructuredCommand b Γ) ->
  ITree (Mem Γ & AmAt & Choice) (Fin b ⊕ Unit)
| [] => .pure (.inr ())
| c :: cs => do
  match (<- denoteStructuredCommand c) with
  | .inl b => .pure (.inl b)
  | .inr _ => denoteStructuredCommands cs
end

def denoteUnstructuredProcedure
   (p: Procedure (Command Γ) Unit Γ)
   (args: ConA p.inParams) :
   -- TODO: make more effect polymorphic
   -- TODO: add inputs to state
   -- TODO: add locals to state
   -- TODO: add outputs to state
   -- TODO: read outputs from state
   ITree (Mem Γ & AmAt & Choice) (ConA p.outParams) := do
    -- Initialize local and output variables with default values
    let globalState : ConA Γ <- liftM Mem.readAll
    let locState : ConA p.locals := default
    let outState : ConA p.outParams := default
    let addlState := args ++ locState ++ outState
    -- Run blocks
    -- TODO: run in totalState instead of Γ
    denoteBlocks p.body (cast sorry 0)
    -- Read output variables
    let outState' : ConA p.outParams := sorry
    return outState'
