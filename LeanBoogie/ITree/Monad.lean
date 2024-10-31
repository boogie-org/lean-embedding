import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Eutt

/-
  # `ITree` forms a monad
-/

def ITree.pure (a : A) : ITree E A := .ret a

def ITree.bind (ta : ITree E A) (tb : A -> ITree E B) : ITree E B :=
  ITree.corec (fun ta => ta.cases
    (fun (a : A) =>
      let tb : ITree E B := tb a

      sorry
    ) -- :(
    (fun ta => .tau ta)
    (fun e k => .vis e (fun x => k x))
  ) ta

instance : Monad (ITree E) where
  pure := ITree.pure
  bind := ITree.bind

#check LawfulMonad

/- ## Helpers for writing imperative programs -/

def ITree.skip : ITree E Unit := .ret ()
def ITree.spin : ITree E A := ITree.corec (fun n => .tau n) 0
def ITree.seq (a b : ITree E Unit) : ITree E Unit := bind a (fun () => b)
def ITree.trigger (e : E) : ITree E Int := .vis e (fun ans => .ret ans)

def ITree.ite (c : ITree E Bool) (t e : ITree E Unit) : ITree E Unit
  := bind c (fun c => if c then t else e)

abbrev ITree.ifthen (c : ITree E Bool) (t : ITree E Unit) : ITree E Unit
  := ite c t skip

def ITree.assume (φ : Prop) [Decidable φ] : ITree E Unit := if φ then skip else spin

/-
  From the ITrees paper, page 12:
  CoFixpoint iter (body : A → itree E (A + B)) : A → itree E B :=
    fun a ⇒ ab <- body a ;;
      match ab with
      | inl a ⇒ Tau (iter body a)
      | inr b ⇒ Ret b
      end.

  Definition loop (body : C + A → itree E (C + B)) : A → itree E B :=
    fun a ⇒ iter (fun ca ⇒
      cb <- body ca ;;
      match cb with
      | inl c ⇒ Ret (inl (inl c))
      | inr b ⇒ Ret (inr b)
      end) (inr a).
-/

-- -- ! Wait,... we don't have loops. We just have blocks.
-- def loop (step : A -> ITree E (Sum A B)) (a : A) : ITree E B :=
--   sorry

-- /--
--         iter step a  : ITree E B
--   step (iter step a) : ITree E B
-- -/
-- def iter (step : A -> ITree E (Sum A B)) (a : A) : ITree E B :=
--   ITree.corec (fun iter_ =>
--     bind (step iter_) (fun
--       | .inl a => step a
--       | .inr b => .ret (.inr b)
--     )
--   ) a
--   -- ITree.corec (fun
--   --   | .inl a => .tau (step a)
--   --   | .inr b => .ret b
--   -- ) (Sum.inl a)

--   -- ITree.bind (step a) (fun
--   --   | .inl a => step a
--   --   | .inr b => sorry
--   -- )
