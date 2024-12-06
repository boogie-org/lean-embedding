import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Monad
import LeanBoogie.ITree.RunFinite
import LeanBoogie.Iter

namespace ITree
open LeanBoogie

/-
  ## ITrees form an *iterative* monad
-/

/-- Repeat a computation until it returns `B`.

  From the ITrees paper, page 12:
  ```
  CoFixpoint iter (body : A → itree E (A + B)) : A → itree E B :=
    fun a ⇒ ab <- body a ;;
      match ab with
      | inl a ⇒ Tau (iter body a)
      | inr b ⇒ Ret b
      end.
  ``` -/
def iter (body : A -> ITree E (A ⊕ B)) (a₀ : A) : ITree E B :=
  ITree.corec (fun (tab : ITree E (A ⊕ B)) =>
    match tab.dest with
    | .ret (.up (.inl a)) => .tau (body a) -- `iter body a`
    | .ret (.up (.inr b)) => .ret (.up b) -- `ret b`
    | .tau t => .tau t
    | .vis ⟨Ans, e, k⟩ => .vis ⟨Ans, e, k⟩
  ) (body a₀)

instance : Iter (ITree E) := ⟨iter⟩


theorem iter_fp {f : A -> ITree E (A ⊕ B)}
  : iter f a₀ = do let ab <- f a₀
                   match ab with
                   | .inl a => (iter f a)
                   | .inr b => return b
  := by sorry

instance : LawfulIter (ITree E) where
  iter_fp' := iter_fp
  while_fp := sorry
