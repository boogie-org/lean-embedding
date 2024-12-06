import LeanBoogie.ITree

namespace LeanBoogie
open ITree (HasEff)

/-- `Assume` and `Assert` effect. You can write programs such as the following,
  where you obtain a proof of the proposition you're assuming.
  ```
  .vis (.read "i") fun (i : Int) =>
    .vis (.am (i < 123)) fun (prf : i < 2) =>
      ...
  ```
  It is up to whoever interprets the event stream to provide the actual proof though!
  For example, if you're executing a memoryful program, you may try to decide the proposition using
  either a decision procedure or SMT solvers.  But if you can't provide a proof, you get stuck
  during execution. If you decide the assumption to be false, you are in an impossible branch,
  so you can safely eliminate that branch, and need not follow it further.

  You can interpret this into a nondeterminism (i.e. set of possible continuations) monad as follows.
  Namely, the set of all continuations for which we are able to provide a proof.
  Note that `Pow A = A -> Prop`.
  ```
  def interp : ITree (AmAt + E) A -> Pow (ITree E A)
  | .vis (.am P) k => { t : ITree E A | (prf : P) -> t = k prf }
  | .vis (.at P) k => { t : ITree E A | (prf : P)  ∧ t = k prf }
  | ...
  ```

  *Key insight*: Both the dijkstra monad and the powerset non-deterministic interpretation describe
    a set of possible computations. Is it the same notion? Only difference is that dijkstra monad
    additionally also is a predicate transformer.

  So you actually want something like the following. However, if we have effects other than `Am`,
  it is unknown whether we can write down `ITreeW`. One solution is to interpret e.g. memory effects
  away before interpreting away `Am`.
  ```
  def interp : ITree AmAt A -> ITree0W A :=
  | .vis (.am P) k =>
    fun (post : ITree Empty A -> Prop) =>
      (prf : P) -> interp (k prf) post
  | .vis (.at P) k =>
    fun (post : ITree Empty A -> Prop) =>
      (prf : P) ∧ interp (k prf) post
  | ...
  ```

  Now let's denote `if` as a nondet jump to two itrees, each starting with an assumes event:
  ```
  def myprog : ITree (AmAt + Choose + Mem) A :=
    .vis (.choose (Fin 2)) fun
      | 0 => .vis (.am   φ ) fun (prf :  φ) => t
      | 1 => .vis (.am (¬φ)) fun (prf : ¬φ) => e
  ```
  Then you get something like a `ITreeW Mem A` or an `ITree0W A`, but no more `Choose` and `AmAt`:
  ```
  interp myprog = (fun s post => ??)
  ```
-/
inductive AmAt : Type -> Type
/-- Assume `P`. -/
| am : (P : Prop) -> AmAt (PLift P)
/-- Assert `P`. -/
| at : (P : Prop) -> AmAt (PLift P)

def assume' [HasEff AmAt Es] (P : Prop) : ITree Es (PLift P) := .vis (AmAt.am P) .ret
abbrev assume [HasEff AmAt Es] (P : Prop) : ITree Es Unit := do let _ <- assume' P
def assert' [HasEff AmAt Es] (P : Prop) : ITree Es (PLift P) := .vis (AmAt.at P) .ret
abbrev assert [HasEff AmAt Es] (P : Prop) : ITree Es Unit := do let _ <- assert' P

/-- This is sound! You can have `ITree E False`, but never `False`.
  This does not spin either, it just asks for the return value (a `False`) from the world.
  Which the world can not give, unless the world itself introduces an assumption of `False`,
  as we (intend to) do when interpreting into the Dijkstra monad `ITreeW`. -/
def ohno [HasEff AmAt E] : ITree E Empty := do
  let .up prf <- assume' False
  prf.elim

#print axioms assume'

#print axioms ohno

-- def interp : ITree AmAt A -> ITree0W A := sorry
-- theorem interp_assume : interp (.vis (.assume P) k) = ⟨fun post => P -> (interp (k default)).1 post, sorry⟩ := sorry
-- theorem interp_assert : interp (.vis (.assert P) k) = ⟨fun post => P /\ (interp (k default)).1 post, sorry⟩ := sorry

-- To generate executable code, we ignore AmAt entirely. If we can't decide an assume/assert to be true, we crash.
-- interpX : ITree (Mem + AmAt) A -> ITree Mem (Option A)
-- interpV : ITree (Mem + AmAt) A -> ITree0W A
