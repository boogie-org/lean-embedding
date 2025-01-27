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
  -- TODO: do we need E'?
  toITree : α -> ITree (E & E') R

-- TODO: don't need separate constructors?
def denoteLiteral : Literal A -> TyA A
| .intL n => n
| .boolL b => b
| .bvL bv => bv
| .realL r => r

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
| _, .eq, a, b => a == b
| _, .neq, a, b => a != b
| _, .lessI, x, y => x < y

def denoteAppliable [Monad m] : Appliable A B -> m (TyA A -> TyA B)
| .binop op => pure (denoteBinaryOp op)
| .unop op => pure (denoteUnaryOp op)
| .relop eq op => pure (denoteRelationOp eq op)
| .mapSelect => pure (λ x => x)

-- We can denote an expression using an arbitrary function to retrieve
-- the value of a variable. We make it monadic so that it can, if desired
-- work in a state or ITree monad.
def denoteExpr [Monad m] : Ctx m Γ -> Expr Γ A -> m (TyA A)
| _, .lit l => pure (denoteLiteral l)
| γ, .apply a e => do
  pure ((<- denoteAppliable a) (<- denoteExpr γ e))
| γ, .applyExpr fe e => do
  pure ((<- denoteExpr γ fe) (<- denoteExpr γ e))
| γ, .var x => γ x

-- Within an ITree, we don't need to pass around a context, and can just
-- use Mem.read.
def denoteExprI : Expr Γ A -> ITree (Mem Γ) (TyA A) :=
  denoteExpr Mem.read

instance exprITree : ToITree (Expr Γ A) (Mem Γ) (TyA A) where
  toITree e := denoteExprI e

def denotePassiveCommand : PassiveCommand Γ -> ITree (Mem Γ & AmAt) Unit
| .assert e => do assert (<- denoteExprI e)
| .assume e => do assume (<- denoteExprI e)

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
