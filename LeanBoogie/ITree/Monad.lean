import LeanBoogie.ITree.ITree

namespace ITree

/-
  # ITrees form a monad
-/

def pure (a : A) : ITree E A := .ret a

def bind (ta : ITree E A) (tb : A -> ITree E B) : ITree E B := sorry -- TODO: fix
  -- ITree.corec (β := Sum (ITree E A) (ITree E B)) (fun x =>
  --   match x with
  --   | .inl ta =>
  --     match ta.dest with
  --     | .ret (.up a : ULift A) =>
  --       let tb : ITree E B := tb a
  --       let ret : ITree.Base E B (ITree E B) := tb.dest
  --       let ret : ITree.Base E B (ITree E A ⊕ ITree E B) := MvFunctor.map (F := TypeFun.ofCurried (n := _) Base) Base.Inr ret
  --       ret
  --     | .tau t => .tau (.inl t)
  --     | .vis e k => .vis e (fun x => .inl (k x))
  --   | .inr b => Base.replay b Sum.inr
  -- ) (Sum.inl ta)

instance : Monad (ITree E) where
  pure := pure
  bind := bind

instance : LawfulFunctor (ITree E) where
  map_const := sorry
  id_map := sorry
  comp_map := sorry

instance : LawfulMonad (ITree E) where
  seqLeft_eq := sorry
  seqRight_eq := sorry
  pure_seq := sorry
  bind_pure_comp := sorry
  bind_map := sorry
  pure_bind := sorry
  bind_assoc := sorry
