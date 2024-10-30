import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Eutt
import LeanBoogie.ITree.Monad

/-
  # Memory effects
-/

example : Ans = Int := rfl -- currently our ITrees have the answer type hardcoded as Int.

/-- Memory events: Reading or writing of a variable. -/
inductive MemEv
| read  : String        -> MemEv
| write : String -> Int -> MemEv

abbrev Mem : Type -> Type := ITree MemEv

def Mem.set (a : String) (b : Int) : Mem Unit := .vis (.write a b) (fun _unit => .ret ())
def Mem.get (v : String)           : Mem Int  := .vis (.read v) (fun ans => .ret ans)

-- TODO: interpreting memory events away into the boogie state monad.
