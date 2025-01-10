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

namespace IterBlockyCongr

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

@[aesop unsafe 10%] theorem interp_iter_congr [Monad M] [Iter M] {h : Handler E M} {t₁ t₂ : A -> ITree E (A ⊕ B)}
  : (∀a, interp h (t₁ a) = interp h (t₂ a)) -> interp h (Iter.iter t₁ a) = interp h (Iter.iter t₂ a)
  := by intro; simp_all only [interp_iter]

theorem interp_iter_congr3 [Monad M] [Iter M] {γ δ θ}
  {h : Handler E (StateT Γ <| StateT Δ <| StateT Θ <| M)}
  {t₁ t₂ : A -> ITree E (A ⊕ B)}
  : (∀a γ δ θ, interp h (t₁ a) γ δ θ = interp h (t₂ a) γ δ θ) -> interp h (Iter.iter t₁ a) γ δ θ = interp h (Iter.iter t₂ a) γ δ θ
  := by sorry

/-
  # Unbounded iter, proof by congruence
-/


procedure foo(n: int) returns (r: int) {
  var i : int;
  goto cond;
cond:
  goto body, finish;
body:
  assume i < n;
  r := r + 10;
  i := i + 1;
  r := r - 5;
  goto cond;
finish:
  assume !(i < n);
  return;
}

procedure bar(n: int) returns (r: int) {
  var i : int;
  goto cond;
cond:
  goto body, finish;
body:
  assume i < n;
  i := i + 1;
  r := r + 5;
  goto cond;
finish:
  assume !(i < n);
  return;
}


example : foo (n, ()) = bar (n, ()) := by
  unfold foo bar
  dsimp only [default, ConA.inhabited, TyA.inhabited]
  congr 1 -- just so happens to work here because we have the same locals and rettype

  -- * use congruence: Prove all blocks equivalent under interp
  rw [interp_iter_congr3]
  intro block locals ret params
  fin_cases block <;> simp only [selectBlock, List.get]
  . rfl
  . rw [foo.body, bar.body]
    simp [-nextBlock]
    simp only [↓Fin.isValue, bind_assoc, pure_bind, ↓reduceIte, Int.ofNat_eq_coe, Nat.cast_zero,
      @State.exe_Δ_rd _, ConA.get, zero_add, State.exe_Δ_wr, ConA.set, @State.exe_Γ_rd _,
      State.exe_Γ_wr, Int.reduceAdd, interp_pure]
    congr! 1
    simp [foo.L, foo.P, ConA, TyA] at locals
    auto
  . rfl
