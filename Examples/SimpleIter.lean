-- import LeanBoogie.BoogieDsl
import LeanBoogie.ITree
import LeanBoogie.Boog
import LeanBoogie.Mem
import Auto
import Aesop

open Boogie ITree

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
  while_ (return (<- Mem.read "i") < 3) do
    Mem.update "i" (. + 1)
    Mem.update "x" (. + 2)
  Mem.write "i" 0 -- need to set `i` to 0 afterwards, otherwise the programs compute the same `x` but not `i`.

def p2 : ITree MemEv Unit := do
  Mem.write "i" 0
  while_ (return (<- Mem.read "i") < 6) do
    Mem.update "x" (. + 1)
    Mem.update "i" (. + 1)
  Mem.write "i" 0

example : EuttB (interp p1) (interp p2) := by
  rw [p1, p2]
  -- 1. unroll loops
  conv => lhs; rw [Eutt.eq while_unroll1, Eutt.eq while_unroll1, Eutt.eq while_unroll1, Eutt.eq while_unroll1, Eutt.eq while_unroll1]
  conv => rhs; rw [Eutt.eq while_unroll1, Eutt.eq while_unroll1, Eutt.eq while_unroll1, Eutt.eq while_unroll1, Eutt.eq while_unroll1, Eutt.eq while_unroll1, Eutt.eq while_unroll1, Eutt.eq while_unroll1]

  -- 2. Push `interp` inwards as far as possible,
  -- this will change `ITree.{pure, bind, iter, ite, read, write}`
  -- into `Boog.{pure, bind, iter, ite, read, write}`
  simp [EuttB.eq interp_bind, EuttB.eq interp_write, EuttB.eq interp_ite, EuttB.eq interp_pure,
    Mem.update, EuttB.eq interp_write, EuttB.eq interp_read, skip]
  -- Our goal is now of form `b1 b2 : (S -> ITree ∅ (A × S)) ⊢ ∀σ:S, Eutt (b1 σ) (b2 σ)`, with the predominant `bind` being `Boog.bind`.

  -- 3. Push state `σ` inwards as far as possible. This allows us to apply `pure_bind` and obtain
  -- a pure state transition function, because we no longer have any relevant coinduction.
  -- Nonetheless, this causes the predominant `bind` to become `ITree.bind` yet again (`Boog.read v : Boog ..`, but `Boog.read v σ : ITree ..`).
  -- However, we know that `ITree.bind (Boog.read v σ) k` is actually `ITree.bind (ITree.pure (σ v, σ)) k`, which simplifies to `k (σ v) σ` via `pure_bind`. Similar for `.write`.
  intro σ
  simp only [Eutt.eq Boog.bind_push_state, Eutt.eq Boog.ite_push_state]
  simp only [Boog.read, Boog.write, BoogieState.update.eq_unfold]
  simp only [pure_bind, Nat.ofNat_pos, dite_eq_ite, ↓reduceDIte, ↓reduceIte, String.reduceEq, zero_add, Nat.one_lt_ofNat, Int.reduceAdd, Int.reduceLT, lt_self_iff_false]
  simp_all only [↓reduceIte]

  dsimp [Pure.pure, ITree.pure]
  -- Our goal is now of form `σ : S ⊢ .ret (a, f σ) = .ret (b, g σ)`
  apply Eutt.ret_congr
  congr 1
  unfold BoogieState at σ
  unfold BoogieState
  -- 4. Solve by auto :)
  auto
