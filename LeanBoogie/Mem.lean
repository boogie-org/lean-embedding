import LeanBoogie.ITree
import LeanBoogie.Boogie
import LeanBoogie.Notation
import LeanBoogie.Util

namespace LeanBoogie

/-
  # Memory effect
-/

/-- Memory events: Reading or writing of a variable. -/
inductive MemEv : Type -> Type
| read  : String        -> MemEv Int
| write : String -> Int -> MemEv Unit
deriving Repr

-- abbrev Mem : Type -> Type := ITree MemEv

def Mem.read (v : String)            : ITree MemEv Int  := .vis (.read v) (fun ans => .ret ans)
def Mem.write (a : String) (b : Int) : ITree MemEv Unit := .vis (.write a b) (fun _unit => .ret ())
/-- Apply a pure function to a variable. Useful for simple operations such as increments, setting to zero, etc. -/
def Mem.update (v : String) (f : Int -> Int) : ITree MemEv Unit
  := Mem.read v >>= fun x => Mem.write v (f x)

/-
  # Interpreting memory
-/

/-- Transforms memory events into state monad actions. -/
def interp (tm : ITree MemEv A) : Boogie A := fun s₀ =>
  ITree.corec (fun ⟨tm, s⟩ =>
    match tm.dest with
    | .ret (.up a) => .ret (.up (a, s))
    | .tau t => .tau (t, s)
    | .vis ⟨_, .up (.read v), k⟩ => .tau ⟨k (s v), s⟩
    | .vis ⟨_, .up (.write v val), k⟩ => .tau ⟨k default, s.update v val⟩
  ) (tm, s₀)


theorem interp_pure : interp (pure x) = pure x := sorry!
theorem interp_ret : interp (.ret x) = pure x := interp_pure

theorem interp_bind {ta : ITree MemEv A} {tb : A -> ITree MemEv B}
  : interp (ta >>= tb) = (interp ta) >>= (fun a => interp (tb a))
  := sorry!


/-- Convenience mix of `interp_bind` and `bind_state_pull`. -/
theorem interp_bind_pull {ta : ITree MemEv A} {tb : A -> ITree MemEv B}
  : interp (ITree.bind ta tb) s = ITree.bind (interp ta s) (fun x => interp (tb x.1) x.2)
  := sorry!


theorem interp_iter {body : A -> ITree MemEv (A ⊕ B)} {a₀ : A}
  : interp (ITree.iter body a₀) = Boogie.iter (fun (a : A) => interp (body a)) a₀
  := sorry!

theorem interp_read : interp (Mem.read x) = Boogie.read x := sorry!
theorem interp_write : interp (Mem.write x val) = (Boogie.write x val) := sorry!

theorem interp_ite [Decidable φ] : interp (if φ then t else e) = (if φ then interp t else interp e) := sorry!
