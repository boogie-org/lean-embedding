import Qpf
import Mathlib.Data.QPF.Multivariate.Constructions.Sigma

/-!
# Interaction Trees

We define interaction trees, a coinductive data-structure used for giving
semantics of side-effecting, possibly non-terminating, programs

[1] https://arxiv.org/abs/1906.00046
[2] https://github.com/DeepSpec/InteractionTrees
-/

namespace Internal

/-
## Hacks / Workarounds

We'd like to define interaction trees as follows:
```
codata ITree (ε : Type → Type) ρ where
  | ret (r : ρ)
  | tau (t : ITree ε ρ)
  | vis {α : Type} (e : ε α) (k : α → ITree ε ρ)
```
Unfortunately, `vis` in that definition is a dependent arrow in disguise,
and dependent arrows are currently not supported by the framework yet.

What is supported, though, are sigma types, as in the following, equivalent,
definition
```
codata ITree (ε : Type → Type) ρ where
  | ret (r : ρ)
  | tau (t : ITree ε ρ)
  | vis (e : Σ α : Type, ε α × α → ITree ε ρ)
```
Unfortunately, this, too yields an error, so for now we settle for fixing a
particular input type `α`, by making `α` a parameter of the type.
-/
codata ITree (α : Type) ε ρ where -- TODO: change ε to be Type -> Type
| ret (r : ρ)
| tau (t : ITree α ε ρ)
| vis : ε → (α → ITree α ε ρ) → ITree α ε ρ

end Internal

/-- For now, due to a limitation in QPF, we hard code the answer type to one specific type. -/
abbrev Ans : Type := Int

def ITree E A := Internal.ITree Ans E A

namespace ITree

-- QPF gotcha: The parameters to ITree get reordered in the ctors somehow
def ret {E A} (r : A) : ITree E A := @Internal.ITree.ret A Ans E r
def tau {E A} (t : ITree E A) : ITree E A := @Internal.ITree.tau Ans E A t
def vis {E A} (e : E) (k : Ans -> ITree E A) := @Internal.ITree.vis E Ans A e k

abbrev Base E A β := Internal.ITree.Base Ans E A β
abbrev Base.Uncurried : TypeFun 3 := Internal.ITree.Base.Uncurried Ans

def corec {E A β : Type} (f : β → ITree.Base E A β) (b : β) : ITree E A
  := MvQPF.Cofix.corec (n := 2) (α := (Vec.reverse (Vec.nil.append1 A ::: E))) (F := TypeFun.ofCurried (n := 3) (ITree.Base)) f b

def dest {E A : Type} : ITree E A -> ITree.Base E A (ITree E A)
  := MvQPF.Cofix.dest

/-- Just a convenience function. Re-plays a tree within another tree. -/
def Base.replay (ta : ITree E A₁) (fTree : ITree E A₁ -> C) (fRet : A₁ -> A₂ := by exact id) : ITree.Base E A₂ C :=
  match ta.dest with
  | .ret (a : A₁) => .ret (fRet a)
  | .tau (t : ITree E A₁) => .tau (fTree t)
  | .vis e k => .vis e (fun x => fTree (k x))

def _root_.TypeVec.ofList : (l : List Type) -> TypeVec l.length
| [] => Vec.nil
| t :: l => TypeVec.ofList l |>.append1 t

def Base.Map (f : C -> D) : TypeVec.Arrow (TypeVec.ofList [C, B, E]) (TypeVec.ofList [D, B, E])
  := TypeVec.appendFun TypeVec.id f

def Base.Inr : TypeVec.Arrow (TypeVec.ofList [ITree E B, B, E]) (TypeVec.ofList [ITree E A ⊕ ITree E B, B, E])
  := TypeVec.appendFun TypeVec.id Sum.inr

@[cases_eliminator, elab_as_elim]
def cases {E A : Type} {motive : ITree E A → Sort u}
    (ret : (r : A) → motive (.ret r))
    (tau : (x : ITree E A) → motive (.tau x))
    (vis : (e : E) → (k : Ans → ITree E A) → motive (.vis e k)) :
    ∀ (x : ITree E A), motive x :=
  fun x =>
    match h : MvQPF.Cofix.dest x with
    | .ret r =>
      have h : x = .ret r := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      h ▸ ret r
    | .tau y =>
      have h : x = .tau y := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      h ▸ tau y
    | .vis e k =>
      have h : x = .vis e k := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      h ▸ vis e k

def spin : ITree E A := corec (fun n => .tau n) 0

/-- Execute a finite amount of steps of a potentially infinite
  Returns the events encountered along the way (if any), and the final state (if any).
  Uses `f` to determine the answer to events. -/
def run (t : ITree E A) (f : E -> Ans) : Nat -> (List E) × Option A
| 0 => ([], none)
| n+1 => match t.dest with
  | .ret a => ([], some a)
  | .tau t => run t f n
  | .vis e k => by
    let t : ITree E A := k (f e)
    let (evs, ret) := run t f n
    exact (e :: evs, ret)

/-- We use theorems from the ITree paper without proof, for now. Give a justification or source in `ref`. -/
axiom trustITree {P : Prop} (ref : String) : P

/-
  ## `ITree` forms a monad
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
    | .inr b => Base.replay b Sum.inr
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


/-
  ## Iter
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


-- # Experimentation:

namespace WithSigma
  inductive ITree2.Shape ρ ι ν
  | ret (r : ρ)
  | tau (t : ι) -- ι = ITree ε ρ
  | vis (e : ν) -- ν = Σ α : Type, ε α × α → ITree ε ρ

  -- qpf F ε ρ ι ν    := (Σ α : Type, ε α × α → ι)
  -- qpf F (α : Type) ε ρ ι ν    := Sigma G

  qpf G (α : Type) (ε : Type → Type) ρ ι ν := ε α × (α → ι)

  #check G
  #check fun α ε => TypeFun.ofCurried (n := 3) (G α ε)
  #check MvQPF.Sigma

  -- def Gs (ε : Type 0 → Type 0) : Type 0 :=
  --   MvQPF.Sigma (A := Type 0) (fun (α : Type _) => TypeFun.ofCurried (n:=3) (G α ε))
end WithSigma
