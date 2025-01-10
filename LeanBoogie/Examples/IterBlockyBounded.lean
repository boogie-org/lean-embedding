import ITree
import LeanBoogie.Dsl
import LeanBoogie.State
import Auto
import Aesop

open LeanBoogie ITree

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.printLemmas true
set_option trace.split.failure true

set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"

namespace IterBlockyBounded

macro "mySimp" : tactic => `(tactic|
  simp? [↓nextBlock, ↓normTyA, ↓reduceIte,
    ConA.get, ConA.set,
    @State.exe_Γ_rd _, @State.exe_Δ_rd _, @State.exe_Θ_rd _, State.exe_Γ_wr, State.exe_Δ_wr, State.exe_Θ_wr, State.exe_Δ_wr_end,
    @Functor.map_pure_3' None, map_spin, ITree.interp_spin, ITree.interp_spin', Functor.map_ite, Functor.map_dite,
    interp_pure, State.spin_state_irrelevant,

    ↓Fin.isValue, ↓pure_bind, bind_pure, decide_not, bind_assoc, Bool.not_eq_true', decide_eq_false_iff_not,
    dite_eq_ite, ite_not, decide_eq_true_eq
  ]
)

macro "trySMT" : tactic => `(tactic|
  try
    congr 1
    auto u[bv.ne, bv.and, bv.add, bv.slt, bv.sext_8_32, bv.trunc_32_8, bv.lshr, bv.shl]
)

macro "tryElimBranch" : tactic => `(tactic|
  try
    first
    | contradiction
    | have : False := by auto u[bv.ne, bv.and, bv.add, bv.slt, bv.sext_8_32, bv.trunc_32_8, bv.lshr, bv.shl]; exact this.elim
)

/-- Split an `if`, then try eliminating each branch if possible. -/
macro "maybeBranch" : tactic => `(tactic| split <;> tryElimBranch)

procedure p1(x0 : int) returns (x: int) {
  var i : int;
  goto init;
init:
  i := 0;
  x := x0;
  goto cond;
cond:
  goto body, finish;
body:
  assume i < 3;
  i := i + 1;
  x := x + 2;
  goto cond;
finish:
  assume !(i < 3);
  return;
}

procedure p2(x0 : int) returns (x: int) {
  var i : int;
  goto init;
init:
  i := 0;
  x := x0;
  goto cond;
cond:
  goto body, finish;
body:
  assume i < 6;
  i := i + 1;
  x := x + 1;
  goto cond;
finish:
  assume !(i < 6);
  return;
}

example : p1 (x0, ()) = p2 (x0, ()) := by
  unfold p1 p2
  -- dsimp [default, ConA.inhabited, TyA.inhabited]
  mySimp
  congr 1; auto
  done
