import LeanBoogie.BoogieDsl

open Boog

set_option auto.smt true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.printLemmas true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"

namespace Example1
  procedure test1(x: int, y: int) returns (z: int) {
    x := (x + 1); x := x + 2;
    y := y + 1; y := y + 2;
    z := x + y;
  }
  procedure test2(x: int, y: int) returns (z: int) {
    y := y + 1; y := y + 2;
    x := x + 2; x := x + 1;
    z := x + y;
  }

  example (state) : test1 state = test2 state := by
    unfold BoogieState at state
    rw [test1, test2]
    simp [Boog.skip, Boog.set, Boog.get, Boog.set, Boog.seq, Boog.ifthen, Boog.ifthenelse,
      bind_eq2,
      StateT.get, StateT.set, getThe, modifyThe, StateT.modifyGet,
      pure, StateT.pure, instMonadStateOfMonadStateOf, instMonadStateOfStateTOfMonad]
    congr 1
    funext v -- for all vars..
    auto
end Example1

namespace Example2
  procedure square(x: int) returns (z : int) {
    if x <= 0 { x := -x; }
    y := 10;
    x := x * x;
  }
  procedure square'(x: int) returns (z : int) {
    x := x * x;
    y := 10;
  }

  example (state : String -> Int) : square state = square' state := by
    unfold BoogieState at *
    rw [square, square']
    simp [Boog.skip, Boog.set, Boog.get, Boog.set, Boog.seq, Boog.ifthen, Boog.ifthenelse,
      bind_eq2, ↓ite_bind, var_congr_ite, state_congr_ite, state_proj_congr_ite,
      StateT.get, StateT.set, getThe, modifyThe, StateT.modifyGet,
      pure, StateT.pure, instMonadStateOfMonadStateOf, instMonadStateOfStateTOfMonad, ↓reduceIte]
    congr 1
    funext v
    rw [state_proj_congr_ite] -- ! simp fails to apply this somehow, but rw works
    simp
    auto
    done
end Example2
