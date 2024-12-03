import LeanBoogie.ITree.ITree

namespace ITree

/-
  # Events
-/

instance (priority := low) : OfNat (Type -> Type) n where ofNat := fun _ => Fin n
instance : OfNat (Type -> Type) 0 where ofNat := fun _ => PEmpty
instance : OfNat (Type -> Type) 1 where ofNat := fun _ => PUnit

/-- The union of two event types. -/
inductive EvProd (E₁ E₂ : Type -> Type) : Type -> Type
| left  : E₁ X -> EvProd E₁ E₂ X
| right : E₂ X -> EvProd E₁ E₂ X

instance : HAdd (Type -> Type) (Type -> Type) (Type -> Type) := ⟨EvProd⟩
