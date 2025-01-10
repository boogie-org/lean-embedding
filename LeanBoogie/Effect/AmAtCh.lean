import LeanBoogie.Effect.AssumeAssert
import LeanBoogie.Effect.Choice

namespace LeanBoogie
open ITree

/-
  # Assume, Assert, and Choice
  Just a convenience. Once we have some way of composing `θ`, similar to `interp` with handlers,
  this file should be deleted.
-/

abbrev AmAtCh : Type -> Type := AmAt & Choice

def AmAtCh._θ : ITree AmAtCh A -> ITree0W A := sorry
instance : Theta (ITree AmAtCh) ITree0W := ⟨AmAtCh._θ⟩
instance : LawfulTheta (ITree AmAtCh) ITree0W := sorry

theorem AmAtCh.θ_am {k : _ -> ITree AmAtCh A}
  : θ (ITree.vis (.left <| .am φ) k)
  = ⟨fun Post => (prf : φ) -> (θ (k ⟨prf⟩)).1 Post,
    by intro; sorry⟩
  := sorry

theorem AmAtCh.θ_at {k : _ -> ITree AmAtCh A}
  : θ (ITree.vis (.left <| .at φ) k)
  = ⟨fun Post => AndD φ fun prf => (θ (k ⟨prf⟩)).1 Post,
    by sorry⟩
  := sorry

theorem AmAtCh.θ_ch {k : _ -> ITree AmAtCh A}
  : θ (ITree.vis (.right <| .ch C) k)
  = ⟨fun Post => ∀c : C, (θ (k c)).1 Post,
    by sorry⟩
  := sorry
