import LeanBoogie.ITree
import LeanBoogie.Boogie
import LeanBoogie.Notation
import LeanBoogie.Util

namespace LeanBoogie

/-
  # Memory effect
-/

example : Ans = Int := rfl -- currently our ITrees have the answer type hardcoded as Int.

/-- Memory events: Reading or writing of a variable. -/
inductive MemEv
| read  : String        -> MemEv
| write : String -> Int -> MemEv
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
    | .ret a => .ret (a, s)
    | .tau t => .tau (t, s)
    | .vis (.read v) k => .tau ⟨k (s v), s⟩
    | .vis (.write v val) k => .tau ⟨k default, s.update v val⟩ -- TODO: Instead of `default : Int`, this should be `() : Unit` once the QPF ITree limitation is gone.
  ) (tm, s₀)

-- def interpk (k : KTree MemEv A B) : Book Empty A B := fun a => interp (k a)


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

-- theorem interpk_iter {body : A -> ITree MemEv (A ⊕ B)} {a₀ : A}
--   -- : ∀a, ∀s, interpk (ITree.iter body) a s ~~ Boogie.iter (interpk body) a s
--   : interpk (ITree.iter body) ~~=~~ Boogie.iter (interpk body)
--   := by sorry

theorem interp_read : interp (Mem.read x) = Boogie.read x := sorry!
theorem interp_write : interp (Mem.write x val) = (Boogie.write x val) := sorry!

theorem interp_ite [Decidable φ] : interp (if φ then t else e) = (if φ then interp t else interp e) := sorry!

theorem interp_ite' : interp (ITree.ite c t e) = (do let c <- interp c; if c then interp t else interp e :) := sorry!

-- theorem interp_cat {f : KTree MemEv A B} {g : KTree MemEv B C}
--   : interp (f a >>> g) ~~ (interp f >>> interpK g) a := sorry
-- theorem interpK_cat {f : KTree MemEv A B} {g : KTree MemEv B C}
--   : interpK (f >>> g) a ~~~ (interpK f >>> interpK g) a := sorry
