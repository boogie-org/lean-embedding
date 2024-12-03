import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Monad

namespace ITree

/-- Execute a finite amount of steps of a potentially infinite
  Returns the events encountered along the way (if any), and the final state (if any).
  Uses `f` to determine the answer to events. -/
def runLog (t : ITree E A) (f : ∀Ans, E Ans -> Ans) : Nat -> (List ((Ans : Type) × E Ans)) × Option A
| 0 => ([], none)
| n+1 => match t.dest with
  | .ret (.up a) => ([], some a)
  | .tau t => runLog t f n
  | .vis ⟨Ans, .up e, k⟩ => by
    let t : ITree E A := k (.up (f _ e))
    let (evs, ret) := runLog t f n
    exact (⟨Ans, e⟩ :: evs, ret)

/-- Run at most `fuel` steps of `t` in a monad, calling `f` for every event. -/
def run [Monad m] (t : ITree E A) (fuel : Nat) (f : ∀{Ans}, E Ans -> m Ans) : m (Option A) :=
  match fuel with
  | 0 => return none
  | fuel+1 => match t.dest with
    | .ret (.up a) => return a
    | .tau t => run t fuel f
    | .vis ⟨_, .up e, k⟩ => do
      let ans <- f e
      let t : ITree E A := k (.up ans)
      run t fuel f
