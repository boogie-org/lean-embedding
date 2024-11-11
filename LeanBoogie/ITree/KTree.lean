import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Eutt
import LeanBoogie.Notation
import LeanBoogie.Iter

abbrev KTree (E A B : Type) : Type := A -> ITree E B

namespace KTree
open ITree

/-- A version of Eutt, but for continuation trees. Just `∀a, Eutt (k1 a) (k2 a)`.  -/
def EuttK (k1 : KTree E A B) (k2 : KTree E A B) : Prop := ∀a, Eutt (k1 a) (k2 a)
infixr:20 " ~~~ " => EuttK

/-- Until we have setoid rewriting in Lean, we use this hack. -/
axiom EuttK.eq {E A B} {t1 t2 : KTree E A B} : EuttK t1 t2 -> t1 = t2

def iter (body : KTree E A (A ⊕ B)) : KTree E A B := ITree.iter body
def loop (body : KTree E (C ⊕ A) (C ⊕ B)) : KTree E A B := ITree.loop body

/-- Concatenation of continuation trees. -/
def cat : KTree E A B -> KTree E B C -> KTree E A C := fun h k => (fun a => ITree.bind (h a) k)
instance : Cat (KTree E) := ⟨cat⟩

def id : KTree E A A := fun a => ITree.pure a
/--
```
  (A -> ITree E C)
  (B -> ITree E C)
  : A+B -> ITree E C
``` -/
def case (tac : KTree E A C) (tbc : KTree E B C) : KTree E (A ⊕ B) C
| .inl a => tac a
| .inr b => tbc b

/-- `A -> ITree E (A+B)` -/
def inl : KTree E A (A ⊕ B) := fun a => ITree.pure (.inl a)
def inr : KTree E B (A ⊕ B) := fun b => ITree.pure (.inr b)
def pure (f : A -> B) : KTree E A B := fun a => ITree.pure (f a)

def bimap (f : KTree E A B) (g : KTree E C D) : KTree E (A ⊕ C) (B ⊕ D)
| .inl a => f a >>= inl
| .inr c => g c >>= inr

-- See page 9 of the ITree paper
@[simp] theorem id_cat : id >>> k ~~~ k := trustITree "page 9"
@[simp] theorem cat_id : k >>> id ~~~ k := trustITree "page 9"
theorem cat_assoc : (i >>> k) >>> k ~~~ i >>> (j >>> k) := trustITree "page 9"
theorem pure_cat : KTree.pure (E := E) f >>> pure g ~~~ pure (f ∘ g) := trustITree "page 9"

@[simp] theorem case_inl : inl >>> case a b ~~~ a := trustITree "page 9"
@[simp] theorem case_inr : inr >>> case a b ~~~ b := trustITree "page 9"

theorem case_split (_h₁ : inl >>> f ~~~ h) (_h₂ : inr >>> f ~~~ k) : f ~~~ case h k := trustITree "page 9"


/-- We can unroll `iter f`. -/
theorem iter_fp {f : KTree E A (A ⊕ B)}      : iter f  ~~~ f   >>> case (iter f) id := trustITree "page 9"

theorem iter_fp_nonK {f : A -> ITree E (A ⊕ B)} : ITree.iter f p ~~ f p >>= case (iter f) id := by sorry

theorem iter_comp : iter (f >>> case g inr) ~~~ f >>> case (iter (g >>> case f inr)) id := trustITree "page 9"

/-- "Iterating f to completion, then executing g" is equivalent to iterationg "execute f, and if it wanted to complete, execute g" to completion. -/
theorem iter_param {f : KTree E A (A ⊕ B)} {g : KTree E B C} : iter f >>> g ~~~ iter (f >>> bimap id g) := trustITree "page 9"

-- See page 8 of the ITree paper
theorem bind_congr : Eutt t1 t2 -> EuttK k1 k2 -> Eutt (ITree.bind t1 k1) (ITree.bind t2 k2) := trustITree "page 8"
theorem vis_congr : EuttK k1 k2 -> Eutt (.vis e k1) (.vis e k2) := trustITree "page 8"
theorem tau_congr : Eutt t1 t2 -> Eutt (.tau t1) (.tau t2) := trustITree "page 8"

end KTree
