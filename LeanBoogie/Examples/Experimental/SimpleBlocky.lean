import LeanBoogie.Dsl
import LeanBoogie.State
import Auto
import Aesop

open LeanBoogie ITree

set_option auto.smt true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.printLemmas true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"
set_option pp.fieldNotation.generalized false

def bb0 : ITree MemEv ((Fin 4) ⊕ Unit) := do
  Mem.write "i" 0
  return .inl 1

def bb1 : ITree MemEv ((Fin 4) ⊕ Unit) := do
  if (<- Mem.read "i") < 3
    then return .inl 2
    else return .inl 3

def bb2 : ITree MemEv ((Fin 4) ⊕ Unit) := do
  Mem.update "x" (. + 2)
  Mem.update "i" (. + 1)
  return .inl 1

def bb3 : ITree MemEv ((Fin 4) ⊕ Unit) := do
  Mem.write "i" 0
  return .inr ()

def p1 : ITree MemEv Unit := ITree.iter blocks 0
  where blocks : Fin 4 -> ITree MemEv ((Fin 4) ⊕ Unit)
  | 0 => bb0
  | 1 => bb1
  | 2 => bb2
  | 3 => bb3

blocky_procedure p2(x: int) {
  var i: int;
  bb0:
    i := 0;
    goto bb1;
  bb1:
    goto bb2, bb3;
  bb2:
    assume i < 3;
    x := x + 2;
    i := i + 1;
    goto bb1;
  bb3:
    assume !i < 3;
    i := 0;
    goto; -- "return"
}

-- For our boogie programs, `A` will usually be the label, and `B` will be `Unit`.
theorem iter_fp {f : A -> ITree E (A ⊕ B)}
  : iter f a
  = f a >>= (match . with | .inl a => iter f a | .inr b => return b)
  := sorry

-- set_option pp.notation false in
example : interp p1 = interp p2 := by
  rw [p1]

  -- unroll once. bb0 always jumps to bb1 so this doesn't branch.
  rw [iter_fp];
  rw [p1.blocks, bb0];
  simp only [Fin.isValue, bind_assoc, pure_bind]

  -- unroll once again (bb1). This time we'll have to branch (see next comment)
  rw [iter_fp]; rw [p1.blocks, bb1];
  simp only [Fin.isValue, ite_bind, bind_assoc, pure_bind]
  /- Now, we need to decide which block to jump to. In this case, we actually have enough information
    to know this, we know that `i < 3` in the following is true. But we need to interpret the memory
    events in order to know this.
    ```
    Mem.write "i" 0
    let i <- Mem.read "i"
    if i < 3 then ... else ...
    ```
    So let's push `interp` inwards, and decide which branch to take.
  -/
  simp only [interp_bind, interp_read, interp_write, interp_ite] -- push `interp` inside
  ext σ -- intro σ
  dsimp [StateT.run]
  simp only [Boogie.bind_push_state, Boogie.ite_push_state] -- push `σ` inside
  simp only [Boogie.read, Boogie.write, BoogieState.update.eq_unfold] -- ! while this works, we should maybe try to avoid looking at the state `σ` ?
  simp
  -- Now our lhs is `interp (iter p1.blocks 2) σ'`, where we know that `σ' "i" = 0`. And we know that the next block is `bb2`.

  try
    -- Unroll twice (-> bb2, -> bb1)
    rw [iter_fp]; rw [p1.blocks, bb2]; simp only [Fin.isValue, ite_bind, bind_assoc, pure_bind]
    rw [iter_fp]; rw [p1.blocks, bb1]; simp only [Fin.isValue, ite_bind, bind_assoc, pure_bind]
    simp [Mem.update, bind_assoc]
    simp only [interp_bind, interp_read, interp_write, interp_ite] -- push `interp` inside
    simp only [Boogie.bind_push_state, Boogie.ite_push_state] -- push `σ` inside
    simp [Boogie.read, Boogie.write, BoogieState.update.eq_unfold] -- "run" the straightline code -- ! while this works, we should maybe try to avoid looking at the state `σ` ?

  try
    -- Unroll twice (-> bb2, -> bb1)
    rw [iter_fp]; rw [p1.blocks, bb2]; simp only [Fin.isValue, ite_bind, bind_assoc, pure_bind]
    rw [iter_fp]; rw [p1.blocks, bb1]; simp only [Fin.isValue, ite_bind, bind_assoc, pure_bind]
    simp [Mem.update, bind_assoc]
    simp only [interp_bind, interp_read, interp_write, interp_ite] -- push `interp` inside
    simp only [Boogie.bind_push_state, Boogie.ite_push_state] -- push `σ` inside
    simp [Boogie.read, Boogie.write, BoogieState.update.eq_unfold] -- "run" the straightline code -- ! while this works, we should maybe try to avoid looking at the state `σ` ?

  try
    -- Unroll twice (-> bb2, -> bb1)
    rw [iter_fp]; rw [p1.blocks, bb2]; simp only [Fin.isValue, ite_bind, bind_assoc, pure_bind]
    rw [iter_fp]; rw [p1.blocks, bb1]; simp only [Fin.isValue, ite_bind, bind_assoc, pure_bind]
    simp [Mem.update, bind_assoc]
    simp only [interp_bind, interp_read, interp_write, interp_ite] -- push `interp` inside
    simp only [Boogie.bind_push_state, Boogie.ite_push_state] -- push `σ` inside
    simp [Boogie.read, Boogie.write, BoogieState.update.eq_unfold] -- "run" the straightline code -- ! while this works, we should maybe try to avoid looking at the state `σ` ?

  -- Unroll once (-> bb3, the final block)
  rw [iter_fp]; rw [p1.blocks, bb3]; simp only [Fin.isValue, ite_bind, bind_assoc, pure_bind]
  simp only [interp_pure, interp_bind, interp_read, interp_write, interp_ite] -- push `interp` inside
  simp only [Boogie.bind_push_state, Boogie.ite_push_state] -- push `σ` inside
  simp [Boogie.read, Boogie.write, BoogieState.update.eq_unfold] -- "run" the straightline code -- ! while this works, we should maybe try to avoid looking at the state `σ` ?
  simp_all only [↓reduceIte]

  -- # Now, p2
  rw [p2]
  simp [ITree.seq]

  -- unroll once
  rw [iter_fp]
  simp? [selectBlock]
  rw [iter_fp]
  simp? [selectBlock]

  sorry
