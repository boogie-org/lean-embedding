import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Eutt

def ITree.pure (a : A) : ITree E A := .ret a

def ITree.bind (ta : ITree E A) (tb : A -> ITree E B) : ITree E B :=
  ITree.corec (fun ta => ta.cases
    (fun (a : A) => sorry) -- :(
    (fun ta => .tau ta)
    (fun e k => .vis e (fun x => k x))
  ) ta

instance : Monad (ITree E) where
  pure := ITree.pure
  bind := ITree.bind

#check LawfulMonad
