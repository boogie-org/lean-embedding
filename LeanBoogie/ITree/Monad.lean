import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Eutt

/-
  # `ITree` forms a monad
-/

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

/- ## Helpers for writing imperative programs -/

def ITree.skip : ITree E Unit := .ret ()
def ITree.seq (a b : ITree E Unit) : ITree E Unit := bind a (fun () => b)
def ITree.trigger (e : E) : ITree E Int := .vis e (fun ans => .ret ans)

def ITree.ite (c : ITree E Bool) (t e : ITree E Unit) : ITree E Unit
  := bind c (fun c => if c then t else e)

abbrev ITree.ifthen (c : ITree E Bool) (t : ITree E Unit) : ITree E Unit
  := ite c t skip
