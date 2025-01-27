import Lean
import ITree
import LeanBoogie.ConTy
import LeanBoogie.Denotation
import LeanBoogie.State
import LeanBoogie.Syntax
import LeanBoogie.Effect.AssumeAssert
import LeanBoogie.Effect.Mem

open ITree
open LeanBoogie

namespace LeanBoogie

def wpPassiveS : PassiveCommand Γ -> Expr Γ .bool -> Expr Γ .bool
| .assert P, Q => mkBin .and P Q
| .assume P, Q => mkBin .imp P Q

def wpPassiveCommandsS : List (PassiveCommand Γ) -> Expr Γ .bool -> Expr Γ .bool
| [], Q => Q
| c :: cs, Q => wpPassiveS c (wpPassiveCommandsS cs Q)

def wpTransferCommandS : (Fin b -> Expr Γ .bool) -> TransferCommand b Γ -> Expr Γ .bool -> Expr Γ .bool
| blkVar, .goto ls, _ => List.foldl (λ a b => mkBin .and a b) (.lit (.boolL True)) (List.map blkVar ls)
| _, .ret, Q => Q

def wpPassiveBlockS (blkVar: Fin b -> Expr Γ .bool) (blk: SimpleBlock Γ b) (Q: Expr Γ .bool) : Expr Γ .bool :=
  mkBin .equiv (blkVar blk.label) (wpPassiveCommandsS blk.simpleCmds (wpTransferCommandS blkVar blk.transferCmd Q))

def wpPassiveD : Ctx Id Γ -> PassiveCommand Γ -> Prop -> Prop
| γ, .assert P, Q => (Id.run (denoteExpr γ P)) ∧ Q
| γ, .assume P, Q => (Id.run (denoteExpr γ P)) → Q

theorem wpPassiveDCorrect :
  { Γ : Con } ->
  { γ : Ctx Id Γ } ->
  { Q : Expr Γ .bool } ->
  ( c : PassiveCommand Γ ) ->
  wpPassiveD γ c (Id.run (denoteExpr γ Q)) = Id.run (denoteExpr γ (wpPassiveS c Q)) :=
  by intros Γ γ Q c
     unfold wpPassiveS wpPassiveD
     unfold mkBin
     cases c <;>
       (simp [denoteExpr, denoteAppliable, denoteBinaryOp] ; repeat rw [Id.run])

def wpPassiveCommandsD : Ctx Id Γ -> List (PassiveCommand Γ) -> Prop -> Prop
| _, [], Q => Q
| γ, c :: cs, Q => wpPassiveD γ c (wpPassiveCommandsD γ cs Q)

def wpTransferCommandD : (Fin b -> Prop) -> TransferCommand b Γ -> Prop -> Prop
| blkVar, .goto ls, _ => List.foldl (λ a b => a ∧ b) True (List.map blkVar ls)
| _, .ret, Q => Q

def wpPassiveBlockD (γ : Ctx Id Γ) (blkVar: Fin b -> Prop) (blk: SimpleBlock Γ b) (Q: Prop) : Prop :=
  blkVar blk.label = wpPassiveCommandsD γ blk.simpleCmds (wpTransferCommandD blkVar blk.transferCmd Q)
