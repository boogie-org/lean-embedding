-- import LeanBoogie.BoogieDsl
import LeanBoogie.ITree
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
-- set_option pp.fieldNotation.generalized false

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

set_option trace.split.failure true

-- set_option maxHeartbeats 99999999
example : interp p1 = interp p2 := by
  rw [p1, p2]
  -- 1. unroll loops
  conv =>
    lhs
    rw [while_fp]
    rw [while_fp]
    rw [while_fp]
    rw [while_fp]
    rw [while_fp]
  conv => rhs; rw [while_fp, while_fp, while_fp, while_fp, while_fp, while_fp, while_fp, while_fp]

  -- 2. Push `interp` inwards as far as possible,
  -- this will change `ITree.{pure, bind, iter, ite, read, write}`
  -- into `Boog.{pure, bind, iter, ite, read, write}`
  simp [interp_pure, interp_bind, interp_write, interp_read, interp_ite,
    Mem.update]
  rw [interp_read] -- for some reason the `simp` above doesn't do this?
  rw [interp_read]
  -- Our goal is now of form `b1 b2 : (S -> ITree ∅ (A × S)) ⊢ ∀σ:S, (b1 σ) (b2 σ)`, with the predominant `bind` being `Boog.bind`.

  -- 3. Push state `σ` inwards as far as possible. This allows us to apply `pure_bind` and obtain
  -- a pure state transition function, because we no longer have any relevant coinduction.
  -- Nonetheless, this causes the predominant `bind` to become `ITree.bind` yet again (`Boog.read v : Boog ..`, but `Boog.read v σ : ITree ..`).
  -- However, we know that `ITree.bind (Boog.read v σ) k` is actually `ITree.bind (ITree.pure (σ v, σ)) k`, which simplifies to `k (σ v) σ` via `pure_bind`. Similar for `.write`.
  ext σ
  unfold StateT.run
  simp only [State.bind_push_state, State.ite_push_state]
  simp only [State.read, State.write]

  /- Note how this `simp only [pure_bind]` transforms
    ```
    let res ← Pure.pure (PUnit.unit, ConA.set σ i 0)
    let res ← Pure.pure (ConA.get res.2 i, res.2)
    let res ← if res.1 < 3 then ...
    ```
    into
    ```
    let res ← if ConA.get (ConA.set σ i 0) i < 3 then ...
    ```
    and then we use `ConA.update_lww` (last write wins) to obtain
    ```
    let res ← if 0 < 3 then ...
    ```
  -/
  have i_ne_x : i ≠ x := sorry
  simp [↓pure_bind, Nat.ofNat_pos, ↓reduceIte, zero_add,
    Nat.one_lt_ofNat, Int.reduceAdd, Int.reduceLT, lt_self_iff_false,
    ConA.update_get, ConA.update_lww,
    ConA.get_irrelevant_set_Var i x i_ne_x, -- ! Will need to add every permutation of this... ?
    ConA.get_irrelevant_set_Var x i (by aesop),
  ]
  dsimp [Pure.pure, ITree.pure]
  congr 2
  /- Now we have an equality on `ConA Γ`
    On the left side of the equality we have the following, which we still need to simplify:
    ```
    σ
    |>.set i 1
    |>.set x (σ.get x + 2)
    |>.set i 2
    |>.set x (σ.get x + 2 + 2)
    |>.set i 3
    |>.set x (σ.get x + 2 + 2 + 2)
    ```
  -/
  conv =>
    lhs
  rw [ConA.grab (γ := (((((σ.set i 1).set x (σ.get x + 2)).set i 2).set x (σ.get x + 2 + 2)).set i 3).set x (σ.get x + 2 + 2 + 2)) i]
  simp [ConA.update_get, ConA.update_lww,
    ConA.get_irrelevant_set_Var i x i_ne_x, -- ! Will need to add every permutation of this... ?
    ConA.get_irrelevant_set_Var x i (by aesop),
  ]
  rw [ConA.grab (γ := ((((((σ.set i 1).set x (σ.get x + 2)).set i 2).set x (σ.get x + 2 + 2)).set i 3).set x (σ.get x + 2 + 2 + 2)).set i 3) x]
  simp [ConA.update_get, ConA.update_lww,
    ConA.get_irrelevant_set_Var i x i_ne_x, -- ! Will need to add every permutation of this... ?
    ConA.get_irrelevant_set_Var x i (by aesop),
  ]
  -- have : (((((σ.set i 1).set x (σ.get x + 2)).set i 2).set x (σ.get x + 2 + 2)).set i 3).set x (σ.get x + 2 + 2 + 2) =
  --     id ((((((σ.set i 1).set x (σ.get x + 2)).set i 2).set x (σ.get x + 2 + 2)).set i 3).set x (σ.get x + 2 + 2 + 2)) := rfl
  -- rw [this]
  -- rw [<- spread_id]
  -- simp only [spread]


  /-
  ret ((), fun v' => if v' = "i" then 0 else if v' = "x" then σ "x" + 2 + 2 + 2 else σ v') =
  ret ((), fun v' => if v' = "i" then 0 else if v' = "x" then σ "x" + 1 + 1 + 1 + 1 + 1 + 1 else σ v')
  -/

  -- Our goal is now of form `σ : S ⊢ .ret (a, f σ) = .ret (b, g σ)`
  -- congr 1
  -- 4. Solve by auto :)
  auto

/-
  σ
  |>.set i 1
  |>.set x (σ.get x + 2)
  |>.set i 2
  |>.set x (σ.get x + 2 + 2)
  |>.set i 3
  |>.set x (σ.get x + 2 + 2 + 2)
-/
