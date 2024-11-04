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

abbrev KTree (E A B : Type) : Type := A -> ITree E B

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
