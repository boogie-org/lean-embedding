import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Eutt
import LeanBoogie.Notation
import LeanBoogie.Iter

namespace ITree

/- # Convenience functions for writing imperative programs -/

def skip : ITree E Unit := Pure.pure ()
def seq (a b : ITree E Unit) : ITree E Unit := Bind.bind a (fun () => b)
instance : Seqi (ITree E Unit) := ⟨ITree.seq⟩
def trigger (e : E) : ITree E Int := .vis e .ret
def ite (c : ITree E Bool) (t e : ITree E A) : ITree E A := Bind.bind c (fun c => if c then t else e)
abbrev ifthen (c : ITree E Bool) (t : ITree E Unit) : ITree E Unit := ite c t skip

def while_ (c : ITree E Bool) (body : ITree E Unit) : ITree E Unit :=
  ITree.iter
    (fun () => ite c
        (do body; return .inl ())
        (return .inr ())
    )
    ()

-- def while_ (c : ITree E Bool) (body : ITree E Unit) : ITree E Unit :=
--   ITree.iter
--     (fun () => do
--       if <- c
--         then body; return .inl ()
--         else return .inr ()
--     )
--     ()

theorem while_unroll1 : while_ c f = (do if <- c then f; while_ c f else return ()) := by sorry
theorem while_unroll1' : while_ c f = ITree.ite c (do f; while_ c f) skip := by sorry

/-- Decide the proposition, spin forever if false. -/
def assume (φ : Prop) [Decidable φ] : ITree E Unit := if φ then skip else spin

end ITree
