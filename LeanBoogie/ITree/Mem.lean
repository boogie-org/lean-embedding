import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Eutt
import LeanBoogie.ITree.Monad
import LeanBoogie.Boog

namespace Boogie

/-
  # Memory effects
-/

example : Ans = Int := rfl -- currently our ITrees have the answer type hardcoded as Int.

/-- Memory events: Reading or writing of a variable. -/
inductive MemEv
| read  : String        -> MemEv
| write : String -> Int -> MemEv
deriving Repr

abbrev Mem : Type -> Type := ITree MemEv

def Mem.set (a : String) (b : Int) : Mem Unit := .vis (.write a b) (fun _unit => .ret ())
def Mem.get (v : String)           : Mem Int  := .vis (.read v) (fun ans => .ret ans)

abbrev Mem.inc (v : String) : Mem Unit := do
  let x <- get v
  set v (x+1)

/-
  # Interpreting memory
-/

/-- Transforms memory events into state monad actions. -/
-- def interp (tm : ITree MemEv A) (s₀ : BoogieState) : ITree Empty (A × BoogieState) :=
def interp (tm : ITree MemEv A) : StateT BoogieState (ITree Empty) A := fun s₀ =>
  ITree.corec (fun ⟨tm, s⟩ =>
    match tm.dest with
    | .ret a => .ret (a, s)
    | .tau t => .tau (t, s)
    | .vis (.read v)      k =>
      let ⟨val, s'⟩ := Boog.get v s
      .tau ⟨k val, s'⟩
    | .vis (.write v val) k =>
      let ⟨(), s'⟩ := Boog.set v (pure val) s
      .tau ⟨k (default), s'⟩ -- TODO: Instead of `default : Int`, this should be `() : Unit` once the QPF ITree limitation is gone.
  ) (tm, s₀)

def writeForever : ITree MemEv Empty
  := ITree.corec (fun a => .vis (MemEv.write "x" 1) (fun _unit => a) ) 0

-- ? If it terminates, can you extract the state transition function?
#check fun s₀ => ITree.run (interp (Mem.inc "x") s₀) 0 2 |>.2
-- #eval ITree.run (interp (Mem.inc "x") {}) 0 2 |>.2

#check interp writeForever
#check ITree.run (interp writeForever {}) 0 0
#reduce ITree.run (interp writeForever {}) 0 0

theorem interp_ret : interp (.ret x) s = .ret (x, s) := by
  rw [interp]
  sorry


section Experiment
-- ## Crazy idea, what if...

def interp_crazy (t : ITree MemEv A) : ITree Empty (A × (BoogieState -> BoogieState -> Prop)) :=
  match t.dest with
  | .ret r => .ret (r, (. = .))
  | .tau r => sorry
  | .vis e k => sorry

end Experiment
