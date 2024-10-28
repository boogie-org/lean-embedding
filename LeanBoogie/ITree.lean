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

def ITree E A := Internal.ITree String E A
-- QPF gotcha: The parameters to ITree get reordered in the ctors somehow
def ITree.ret {E A} (r : A) : ITree E A := @Internal.ITree.ret A String E r
def ITree.tau {E A} (t : ITree E A) : ITree E A := @Internal.ITree.tau String E A t
def ITree.vis {E A} (e : E) (k : String -> ITree E A) := @Internal.ITree.vis E String A e k

abbrev ITree.Base E A β := Internal.ITree.Base String E A β

def ITree.corec {E A β : Type} (f : β → ITree.Base E A β) (b : β) : ITree E A :=
  MvQPF.Cofix.corec (n := 2) (F := TypeFun.ofCurried (ITree.Base)) f b

#check 1

#check MvQPF.Cofix (n := 2) (F := TypeFun.ofCurried (ITree.Base))
#check MvQPF.Fix (n := 2) (F := TypeFun.ofCurried (ITree.Base)) (fun | 0 => String | 1 => String)
#check MvQPF.Cofix (n := 2) (F := TypeFun.ofCurried (ITree.Base)) (fun | 0 => String | 1 => String)
-- #reduce (types := true) MvQPF.Cofix (n := 2) (F := TypeFun.ofCurried (ITree.Base)) (fun | 0 => String | 1 => String)



@[cases_eliminator, elab_as_elim]
def ITree.cases {E A : Type} {motive : ITree E A → Sort u}
    (ret : (r : A) → motive (.ret r))
    (tau : (x : ITree E A) → motive (ITree.tau x))
    (vis : (e : E) → (k : String → ITree E A) → motive (.vis e k)) :
    ∀ (x : ITree E A), motive x :=
  fun x =>
    match h : MvQPF.Cofix.dest x with
    | .ret r =>
      have h : x = ITree.ret r := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      h ▸ ret r
    | .tau y =>
      have h : x = ITree.tau y := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      h ▸ tau y
    | .vis e k =>
      have h : x = ITree.vis e k := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      h ▸ vis e k

inductive EquivUTT.F (R : ITree E A → ITree E A → Prop) : ITree E A → ITree E A → Prop
| ret : EquivUTT.F R (.ret r) (.ret r)
| vis : (∀ a, R (k₁ a) (k₂ a)) → EquivUTT.F R (.vis e k₁) (.vis e k₂)
| tau  : R x y → EquivUTT.F R (.tau x) (.tau y)
| taul : R x y → EquivUTT.F R (.tau x) y
| taur : R x y → EquivUTT.F R x (.tau y)

/-- Equivalence-up-to-tau, i.e., weak bisimiulation. This is called `eutt` in the Coq development -/
inductive EquivUTT (x y : ITree E A) : Prop where
| intro
  (R : ITree E A → ITree E A → Prop)
  (h_fixpoint : ∀a b, R a b → EquivUTT.F R a b)
  (h_R : R x y)

theorem EquivUTT.refl (x : ITree E A) : EquivUTT x x := by
  apply EquivUTT.intro (R := (· = ·))
  · rintro a - rfl
    cases a
    · constructor
    · constructor; rfl
    · constructor; intro; rfl
  · rfl

theorem EquivUTT.symm {x y : ITree E A} : EquivUTT x y → EquivUTT y x := by
  rintro ⟨R, isFixpoint, h_R⟩
  apply EquivUTT.intro (R := flip R)
  · rintro a b h_fR
    cases isFixpoint _ _ h_fR
    <;> constructor
    <;> assumption
  · exact h_R

theorem EquivUTT.trans {x y z : ITree E A} : EquivUTT x y → EquivUTT y z → EquivUTT x z := by
  rintro ⟨R₁, isFixpoint₁, h_R₁⟩ ⟨R₂, isFixpoint₂, h_R₂⟩
  let R' (a c) := ∃ b, R₁ a b ∧ R₂ b c
  apply EquivUTT.intro (R := R')
  · rintro a c ⟨b, h_fR₁, h_fR₂⟩
    specialize isFixpoint₁ _ _ h_fR₁
    specialize isFixpoint₂ _ _ h_fR₂
    clear h_fR₁ h_fR₂
    -- have r'_of_left (a c) : R' a c

    cases isFixpoint₁
    case ret r =>
      generalize r = retr
      -- split at isFixpoint₂
      -- cases isFixpoint₂
      · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  · exact ⟨y, h_R₁, h_R₂⟩


-- attribute [irreducible] ITree
-- attribute [irreducible] ITree.ret
-- attribute [irreducible] ITree.tau
-- attribute [irreducible] ITree.vis

-- # Examples

/-- `ITree.spin` is an infinite sequence of tau-nodes. -/
def spin : ITree E A := ITree.corec (fun () => .tau ()) ()


-- # Experimentation:

namespace WithSigma
  inductive ITree2.Shape ρ ι ν
  | ret (r : ρ)
  | tau (t : ι) -- ι = ITree ε ρ
  | vis (e : ν) -- ν = Σ α : Type, ε α × α → ITree ε ρ

  -- qpf F ε ρ ι ν    = (Σ α : Type, ε α × α → ι)
  -- qpf F (α : Type) ε ρ ι ν    = Sigma G

  qpf G (α : Type) (ε : Type → Type) ρ ι ν := ε α × (α → ι)

  #check G
  #check fun α ε => TypeFun.ofCurried (n := 3) (G α ε)
  #check MvQPF.Sigma

  -- def Gs (ε : Type 0 → Type 0) : Type 0 :=
  --   MvQPF.Sigma (A := Type 0) (fun (α : Type _) => TypeFun.ofCurried (n:=3) (G α ε))
end WithSigma
