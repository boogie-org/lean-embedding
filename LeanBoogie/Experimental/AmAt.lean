import LeanBoogie.ITree
import LeanBoogie.ITree.ITree0W

open ITree

/-- `Assume` effect. You can write programs such as the following, where you obtain a proof of
  the proposition you're assuming.
  ```
  .vis (.read "i") fun (i : Int) =>
    .vis (.assume (i < 123)) fun (prf : i < 2) =>
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
  def interp : ITree (Am + E) A -> Pow (ITree E A)
  | .vis (.assume P) k => { t : ITree E A | (prf : P) × t = k prf }
  | ...
  ```

  If you instead try to observe this into a Dijkstra monad, you kind of fail at first
  ```
  def θ : ITree Am A -> ITree0W A :=
    fun (post : ITree0 A -> Prop) =>
      (prf : P???) × post ???
  ```

  *Key insight*: Both the dijkstra monad and the powerset non-deterministic interpretation describe
    a set of possible computations. Is it the same notion? Only difference is that dijkstra monad
    also is a predicate transformer.

  So you actually want something like the following. However, if we have effects other than `Am`,
  it is unknown whether we can write down `ITreeW`. One solution is to interpret e.g. memory effects
  away before interpreting away `Am`.
  ```
  def interp_or_θ : ITree (Am + E) A -> ITree0W A :=
  | .vis (.assume P) k =>
    fun (post : ITree Empty A -> Prop) =>
      (prf : P) -> post (interp_or_θ (k prf))
  | ...
  ```

  Now let's denote `if` as a nondet jump to two itrees, each starting with an assumes event:
  ```
  def myprog : ITree (Am + Choose + Mem) A :=
    .vis (.choose (Fin 2)) fun
      | 0 => .vis (.assume   φ ) fun (prf :  φ) => t
      | 1 => .vis (.assume (¬φ)) fun (prf : ¬φ) => e
  ```
  Then you get something like a `ITreeW Mem A` or an `ITree0W A`, but no more `Choose` and `Am`:
  ```
  interp_or_θ myprog = (fun s post => ??)
  ```
-/
inductive Am : Type
| assume : (P : Prop) -> Am

/-- `Assert` effect. You can write programs such as:
  ```
  .vis (.read "i") fun (i : Int) =>
    .vis (.assert (i < 123)) fun () =>
      ...
  ```

  If you interpret this into a nondeterminism monad...
  ```
  def interp : ITree (At + E) A -> Pow (ITree E A)
  | .vis (.assert P) k => { t : ITree E A | t = k ()  ∧  ??? }
  | ...
  ```
-/
inductive At : Type
| assert : (P : Prop) -> At

inductive AmAt : Type
| assume : (P : Prop) -> AmAt
| assert : (P : Prop) -> AmAt

-- def interp : ITree AmAt A -> ITree0W A
