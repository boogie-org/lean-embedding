-- import LeanBoogie.BoogieDsl
import LeanBoogie.ITree
import LeanBoogie.State
import LeanBoogie.Spec.ITree0W
-- import LeanBoogie.Boogie
-- import LeanBoogie.Woogie
-- import LeanBoogie.Mem
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

def Γ : Con := [.int, .int]
def i : Var Γ .int := .vz
def x : Var Γ .int := .vs .vz

def p1 : ITree (Mem Γ) Unit := do
  Mem.write i 0
  While (Mem.read i >>= (fun i => return i < 3)) do
    Mem.update i (. + 1)
    Mem.update x (. + 2)
  Mem.write i 0 -- need to set `i` to 0 afterwards, otherwise the programs compute the same `x` but not `i`.

def p2 : ITree (Mem Γ) Unit := do
  Mem.write i 0
  While (return (<- Mem.read i) < 6) do
    Mem.update x (. + 1)
    Mem.update i (. + 1)
  Mem.write i 0

theorem StateT.bind_push_state [Monad M] [LawfulMonad M] {a : StateT S M A} {b : A -> StateT S M B} : (a >>= b) σ = (a σ >>= fun res => b res.fst res.snd) := rfl
theorem ITree0W.bind_push_fst {wa : ITree0W A} {wb : A -> ITree0W B}
  : (wa >>= wb).fst
  = (fun post => wa.fst (fun ta => (∃ a, Converges a ta ∧ (wb a).fst post) ∨ Diverges ta))
  := rfl

#check θ_bind

set_option maxHeartbeats 10000000
set_option pp.fieldNotation false in
example : θ (interp (State.handler (M := ITree None)) p1 default) <= θ (interp (State.handler (M := ITree None)) p2 default) := by
  rw [p1, p2]
  -- conv => lhs; rw [while_unroll1, while_unroll1, ]; simp
  -- conv => rhs; rw [while_unroll1, while_unroll1, while_unroll1]; simp
  simp [Mem.update]
  simp [interp_bind, interp_ite, interp_pure, While, interp_iter, Mem.write, Mem.read, State.handler]

  rw [@θ_bind (ITree0) _ (ITree0W) _ instThetaITree0ITree0W instLawfulThetaITree0W PUnit]
  intro post hp
  dsimp [θ, ITree0.θ] at *

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
