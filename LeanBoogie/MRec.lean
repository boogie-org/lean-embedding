import LeanBoogie.ITree
import LeanBoogie.State
import Mathlib.Data.Real.Basic

namespace LeanBoogie
open ITree (Effect HasEff)


/-
  # MRec
  Self-recursion and mutual recursion.

  See section 3.3 of the [ITree paper](https://dl.acm.org/doi/pdf/10.1145/3371119).
-/

-- Approach 1:
-- inductive MRec (P : Con) : Type -> Type
-- | call : Var P (A ~> B) -> A -> MRec P B
-- def call [HasEff (MRec P) Es] (p : Var P (.map A B)) (a : A) : ITree Es B :=
--   .vis (MRec.call p a) .ret
-- def rec
--   (procs : Var P (X ~> Y) -> X -> ITree (Mem Γ + MRec P) Y)
--   (main : ITree (Mem Γ + MRec P) A)
--   : ITree (Mem Γ) A
--   := sorry -- ...iter...
-- structure Proc where
--   A : Type
--   B : Type

inductive MRec {Proc : Type} (pTys : Proc -> Type × Type) : Type -> Type
| call : (p : Proc) -> (pTys p).1 -> MRec pTys (pTys p).2

def call {Proc} (P : Proc -> Type × Type) [HasEff (MRec P) E] (p : Proc) (a : (P p).1) : ITree E (P p).2 :=
  .vis (MRec.call p a) .ret

/-- This `mrec` is very different from the ITree paper. -/
def mrec {E : Type -> Type} {Proc} (P)
  (p : Proc)
  (procs : (p : Proc) -> (P p).1 -> ITree (E + MRec P) (P p).2)
  : (P p).1 -> ITree E (P p).2
  := ITree.iter (fun ab => sorry) -- probably a bad idea actually, go with the ITree paper approach instead?

-- Example:
inductive Procs | f | g
def P : Procs -> Type × Type | _ => ⟨Int, Int⟩

def mutualBlock : Int -> ITree E Int := mrec P Procs.f fun
| Procs.f, (x : Int) => do -- def of `f`
  let n : Int <- call P .g (x * 3) -- `g(x * 3)`
  return n
| Procs.g, (x : Int) => do -- def of `g`
  let n : Int <- call P .f (x / 2) -- `f(x / 2)`
  return - n
