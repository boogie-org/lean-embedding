import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Eutt

namespace ITree

/-
  # `ITree` forms a monad
-/


def pure (a : A) : ITree E A := .ret a

def bind (ta : ITree E A) (tb : A -> ITree E B) : ITree E B :=
  ITree.corec (β := Sum (ITree E A) (ITree E B)) (fun x =>
    match x with
    | .inl ta =>
      match ta.dest with
      | .ret (a : A) =>
        let tb : ITree E B := tb a
        let ret : ITree.Base E B (ITree E B) := tb.dest
        let ret : ITree.Base E B (ITree E A ⊕ ITree E B) := MvFunctor.map (F := TypeFun.ofCurried (n := 3) ITree.Base) Base.Inr ret
        ret
      | .tau t => .tau (.inl t)
      | .vis e k => .vis e (fun x => .inl (k x))
    | .inr b =>
      Base.replay b Sum.inr
      -- match b.dest with
      -- | .ret (b : B) => .ret b
      -- | .tau (t : ITree E B) => .tau (.inr t)
      -- | .vis e k => .vis e (fun x => .inr (k x))
  ) (Sum.inl ta)

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

/- ## Helpers for writing imperative programs -/

def skip : ITree E Unit := .ret ()
def spin : ITree E A := corec (fun n => .tau n) 0
def seq (a b : ITree E Unit) : ITree E Unit := bind a (fun () => b)
def trigger (e : E) : ITree E Int := .vis e (fun ans => .ret ans)
def ite (c : ITree E Bool) (t e : ITree E Unit) : ITree E Unit := bind c (fun c => if c then t else e)
abbrev ifthen (c : ITree E Bool) (t : ITree E Unit) : ITree E Unit := ite c t skip

def assume (φ : Prop) [Decidable φ] : ITree E Unit := if φ then skip else spin

/- ## Iter
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

/-- Repeat a computation until it returns `B`. -/
def iter (body : A -> ITree E (A ⊕ B)) (a₀ : A) : ITree E B := sorry
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

def loop (body : Sum C A -> ITree E (Sum C B)) (a : A) : ITree E B := sorry
