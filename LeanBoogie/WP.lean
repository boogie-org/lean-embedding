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

def wpPassiveS : PassiveCommand Γ -> Formula Γ -> Formula Γ
| .assert P, Q => .andF P Q
| .assume P, Q => .impF P Q

def wpPassiveCommandsS : List (PassiveCommand Γ) -> Formula Γ -> Formula Γ
| [], Q => Q
| c :: cs, Q => wpPassiveS c (wpPassiveCommandsS cs Q)

def wpTransferCommandS : (Fin b -> Formula Γ) -> TransferCommand b Γ -> Formula Γ -> Formula Γ
| blkVar, .goto ls, _ => List.foldl (λ a b => .andF a b) (.litF true) (List.map blkVar ls)
| _, .ret, Q => Q

def wpPassiveBlockS (blkVar: Fin b -> Formula Γ) (blk: PassiveBlock Γ b) (Q: Formula Γ) : Formula Γ :=
  .eqF (blkVar blk.label) (wpPassiveCommandsS blk.simpleCmds (wpTransferCommandS blkVar blk.transferCmd Q))

def wpPassiveD : ConA Γ -> PassiveCommand Γ -> Prop -> Prop
| γ, .assert P, Q => denoteFormula γ P ∧ Q
| γ, .assume P, Q => denoteFormula γ P → Q

theorem wpPassiveDCorrect :
  { Γ : Con } ->
  { γ : ConA Γ } ->
  { Q : Formula Γ } ->
  ( c : PassiveCommand Γ ) ->
  wpPassiveD γ c (denoteFormula γ Q) = (denoteFormula γ (wpPassiveS c Q)) :=
  by intros Γ γ Q c
     unfold wpPassiveS wpPassiveD
     cases c <;> simp [denoteExpr, denoteFormula]

def wpPassiveCommandsD : ConA Γ -> List (PassiveCommand Γ) -> Prop -> Prop
| _, [], Q => Q
| γ, c :: cs, Q => wpPassiveD γ c (wpPassiveCommandsD γ cs Q)

def wpTransferCommandD : (Fin b -> Prop) -> TransferCommand b Γ -> Prop -> Prop
| blkVar, .goto ls, _ => List.foldl (λ a b => a ∧ b) True (List.map blkVar ls)
| _, .ret, Q => Q

def wpPassiveBlockD (γ : ConA Γ) (blkVar: Fin b -> Prop) (blk: PassiveBlock Γ b) (Q: Prop) : Prop :=
  blkVar blk.label = wpPassiveCommandsD γ blk.simpleCmds (wpTransferCommandD blkVar blk.transferCmd Q)
