import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Monad

namespace ITree

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
def iter (body : A -> ITree E (A ⊕ B)) (a₀ : A) : ITree E B := sorry -- TODO
  -- ITree.corec (fun (x : A ⊕ ITree E (B)) =>
  --   match x with
  --   | .inl a =>
  --     -- Run the body, if it returned `a` we iter again, if it returned `b` we are done.
  --     let res : ITree E (A ⊕ B) := bind (body a) (fun ab =>
  --       match ab with
  --       | .inl a => .ret (.inl a)
  --       | .inr b => .ret (.inr b)
  --     )
  --     match res.dest with
  --     -- | .ret (a : A ⊕ B) => .ret sorry
  --     | .ret (.inl a) => .tau (.inl a) -- call `iter body a`
  --     | .ret (.inr b) => .ret b -- we are done
  --     | .tau (t : ITree E _) => .tau (.inr t)
  --     | .vis e k => sorry
  --   | .inr b => Base.replay b .inr
  -- ) (Sum.inl a₀)

theorem iter_fp {f : A -> ITree E (A ⊕ B)}
  : iter f a₀ = do let ab <- f a₀
                   match ab with
                   | .inl a => (iter f a)
                   | .inr b => return b
  := by sorry

/--
  Definition loop (body : C + A → itree E (C + B)) : A → itree E B :=
    fun a ⇒ iter (fun ca ⇒
      cb <- body ca ;;
      match cb with
      | inl c ⇒ Ret (inl (inl c))
      | inr b ⇒ Ret (inr b)
      end) (inr a).
-/
def loop (body : Sum C A -> ITree E (Sum C B)) (a : A) : ITree E B := sorry

def iter_lift (body : A -> ITree E (A ⊕ B)) : (A ⊕ B) -> ITree E (A ⊕ B) :=
  fun | .inl a => body a | .inr b => return .inr b
