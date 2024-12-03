import LeanBoogie.Notation

/-- The monad `M` is equipped with `iter`. -/
class Iter (M : Type u -> Type v) [Monad M] where
  iter : {A B : Type u} -> (A -> M (A ⊕ B)) -> A -> M B
open Iter

-- class LawfulIter (M : Type -> Type) {equiv : {A : Type} -> M A -> M A -> Prop} [Monad M] [Iter M] : Prop where
--   iter_fp : equiv (iter f a) (iter f a)
-- /-- We can unroll `iter f`. -/
-- theorem iter_fp {f : KTree E A (A ⊕ B)} : iter f ~~~ f >>> case (iter f) id := trustITree "page 9"
-- theorem iter_fp_nonK {f : KTree E A (A ⊕ B)} : iter f p ~~ f p >>= case (iter f) id := by sorry
-- theorem iter_comp : iter (f >>> case g inr) ~~~ f >>> case (iter (g >>> case f inr)) id := trustITree "page 9"
-- /-- "Iterating f to completion, then executing g" is equivalent to iterationg "execute f, and if it wanted to complete, execute g" to completion. -/
-- theorem iter_param {f : KTree E A (A ⊕ B)} {g : KTree E B C} : iter f >>> g ~~~ iter (f >>> bimap id g) := trustITree "page 9"
