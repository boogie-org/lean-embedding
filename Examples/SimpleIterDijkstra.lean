-- import LeanBoogie.BoogieDsl
import LeanBoogie.ITree
import LeanBoogie.ITree.ITree0W
import LeanBoogie.Boogie
import LeanBoogie.Woogie
import LeanBoogie.Mem
import Auto
import Aesop

open LeanBoogie
open ITree

set_option auto.smt true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.printLemmas true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"
set_option pp.fieldNotation.generalized false

-- Very simple example which can be proven using unrolling or a congruence on the while loop

def p1 : ITree MemEv Unit := do
  Mem.write "i" 0
  while_ (return (<- Mem.read "i") < 1) do
    Mem.update "i" (. + 1)
    Mem.update "x" (. + 2)
  Mem.write "i" 0 -- need to set `i` to 0 afterwards, otherwise the programs compute the same `x` but not `i`.

def p2 : ITree MemEv Unit := do
  Mem.write "i" 0
  while_ (return (<- Mem.read "i") < 2) do
    Mem.update "x" (. + 1)
    Mem.update "i" (. + 1)
  Mem.write "i" 0

theorem StateT.bind_push_state [Monad M] [LawfulMonad M] {a : StateT S M A} {b : A -> StateT S M B} : (a >>= b) σ = (a σ >>= fun res => b res.fst res.snd) := rfl
theorem Woogie.bind_push_state {a : Woogie A} {b : A -> Woogie B} : (a >>= b) σ = (a σ >>= fun res => b res.fst res.snd) := rfl
theorem Woogie.ite_push_state [Decidable c] {t e : Woogie A} : (if c then t else e) σ = (if c then t σ else e σ) := by aesop
theorem ITree0W.bind_push_fst {wa : ITree0W A} {wb : A -> ITree0W B}
  : (wa >>= wb).fst
  = (fun post => wa.fst (fun ta => (∃ a, Converges a ta ∧ (wb a).fst post) ∨ Diverges ta))
  := rfl


set_option maxHeartbeats 10000000
set_option pp.fieldNotation false in
example : θ (interp p1) <= θ (interp p2) := by
  rw [p1, p2]
  conv => lhs; rw [while_unroll1, while_unroll1, ]; simp
  conv => rhs; rw [while_unroll1, while_unroll1, while_unroll1]; simp
  simp [interp_bind, interp_write, interp_ite, interp_pure,
    Mem.update, interp_write, interp_read, ITree.skip]

  simp [θ_bind, Woogie.θ_read, Woogie.θ_write, Woogie.θ_ite] at * -- thread theta through

  intro s post hp
  simp [Woogie.bind_push_state, Woogie.ite_push_state] at *

  dsimp [Pure.pure, Bind.bind] at *
  unfold ITree0W.bind at *
  simp
  -- ∃ a, Converges a ta ∧ ...
  -- ! assuming converges tw >>= ...
  unfold Woogie.write at *
  unfold Woogie.read at *
  unfold BoogieState.update at *
  simp at *

  simp [Converges.eq_unfold, Diverges.eq_unfold] at *
  sorry
  done

#check 1
