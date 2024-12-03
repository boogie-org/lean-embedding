import Qpf
import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Eutt
import LeanBoogie.ITree.Events

open MvQPF
open ITree

instance : Repr Empty where reprPrec _ _ := ""

inductive Ev : Type
| input  : Ev
| output : Int -> Ev -- We would really like this to be `-> Ev Unit`, but can't due to the `(A : Type) -> ...` QPF issue.
deriving Repr

/-- Just echo once. -/
def echo1 : ITree Ev Unit :=
  .vis .input fun (answer : Int) =>
    .vis (.output answer) fun _ =>
      .ret ()

def echo : ITree Ev Empty :=
  ITree.corec (fun
    | none        => .vis (.input        ) fun (answer : Int) => some answer
    | some answer => .vis (.output answer) fun (_unit : /- This should be Unit. -/ Int) => none
    ) none

/-- Finds a `k`, such that `f k = K`, but only searches >=0. -/
def find (f : Nat -> Int) (K : Int) (a : Nat) : ITree Empty Nat :=
  ITree.corec (fun a =>
    if f a = K then .ret a
    else .tau (a+1)
  ) a

theorem find_eq1 {f : Nat -> Int} {K : Int} {a : Nat} (h : f a = K) : find f K a = .ret a := sorry
theorem find_eq2 {f : Nat -> Int} {K : Int} {a : Nat} (h : f a ≠ K) : find f K a = .tau (find f K (a + 1)) := by sorry

/-- Proof by induction on k, i.e. where the searched-for value is. -/
theorem find_correct_aux (f : Nat -> Int) (K : Int) (k a : Nat) (h_a : a <= k) (solvable : f k = K) : Eutt (find f K a) (.ret k) := by
  induction k generalizing a with
  | zero =>
    have : a = 0 := by omega
    cases this
    rw [find_eq1 solvable]
    exact Eutt.refl _
  | succ k ih => -- k is still ahead of the current position (a)
    done

theorem find_correct (f : Nat -> Int) (K : Int) (k : Nat) (solvable : f k = K) : Eutt (find f K 0) (.ret k) :=
  find_correct_aux f K k 0 (by omega) solvable

/-- Like `find`, but on `Int` instead of `Nat`, and searches in both directions. -/
def find2 (f : Int -> Int) (K : Int) (a b : Int) : ITree Empty Int :=
  ITree.corec (fun (a, b) =>
    if f a = K then .ret a
    else if f b = K then .ret b
    else .tau (a - 1, b + 1)
  ) (a, b)

#eval run spin (fun _ => 0) 100
#eval run echo1 (fun | .input => 123 | .output _o => -999 ) 20
#eval run echo (fun | .input => 123 | .output _o => -999 ) 20
#eval run (find (fun x => 2 * x) 1 0) (fun _ => 0) 100
#eval run (find2 (fun x => 2 * x) 1 0 0) (fun _ => 0) 100
#eval run (find2 (fun x => 2 * x) 20 0 0) (fun _ => 0) 11
