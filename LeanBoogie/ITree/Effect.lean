import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Iter

namespace ITree

/-
  # Effects
-/

-- /-- Just a tag. -/
-- class IsEffect (E : Type -> Type)

/-- No effects. This is essentially `Empty`. -/
def None : Type -> Type := fun _ => PEmpty
instance : Inhabited (Type -> Type) := ⟨None⟩
instance : EmptyCollection (Type -> Type) := ⟨None⟩

instance : OfNat (Type -> Type) 0 where ofNat := None

/-- The union of two event types. -/
inductive Effect.Prod (E₁ E₂ : Type -> Type) : Type -> Type
| left  : E₁ Ans -> Prod E₁ E₂ Ans
| right : E₂ Ans -> Prod E₁ E₂ Ans

def Effect.NProd (Es : List (Type -> Type)) : (Type -> Type) :=
  fun Ans => (i : Fin Es.length) -> Es[i] Ans

-- Maybe `Union` would be better?
-- instance : Add Effect := ⟨Effect.Prod⟩
-- instance : Add (Type -> Type) := ⟨Effect.Prod⟩
infix:30 " & " => Effect.Prod

#check None & None

/-- Asserts that the collection of events `Es` has event `E`.

  Note: Usage of this typeclass in conjunction with `Effect.Prod` seems a little buggy, I haven't
  gotten around to why it is wonky yet.
-/
class HasEff (E : semiOutParam (Type -> Type)) (Es : Type -> Type) where
  inj : {Ans : Type} -> E Ans -> Es Ans
  /-- The rest of the events in `Es`, without `E`. -/
  Strip : Type -> Type
  elim : {Ans : Type} -> {motive : Type} -> (E Ans -> motive) -> (Strip Ans -> motive) -> Es Ans -> motive

instance instCoeEff {E Es : Type -> Type} [HasEff E Es] {Ans : Type} : Coe (E Ans) (Es Ans)
  := ⟨HasEff.inj⟩
attribute [coe] HasEff.inj

instance (priority := low) instHasEff_id {E : Type -> Type} : HasEff E E where
  inj := id
  Strip := None
  elim l _ := l

instance instHasEff_left {E₁ E₂ : Type -> Type} : HasEff E₁ (E₁ & E₂) where
  inj := .left
  Strip := E₂
  elim l r := fun | .left e1 => l e1 | .right e2 => r e2

instance instHasEff_right {E₁ E₂ : Type -> Type} : HasEff E₂ (E₁ & E₂) where
  inj := .right
  Strip := E₁
  elim l r := fun | .left e1 => r e1 | .right e2 => l e2


/-
  # Interp, Handlers
  The ITree paper just defines one `interp` using `iter`, for which you can then obtain concrete
  interpretations by giving it a `h`andler.
  I wasn't able to figure out how `iter` is supposed to be used here. The code in the ITree repo
  is slightly different from the code in the paper; I think the paper code may have some typos.
-/


/-- Interpreting events into another monad, which may again be the ITree monad but with e.g.
  fewer or different effects.
-/
def interp [Monad M] (h : {A : Type} -> E A -> M A) : ITree E A -> M A :=
  sorry

/-
  # Embedding
-/

/-- We can embed an ITree with fewer effects into an ITree with more.

  *TODO*: We should have the following theorem: `interp_Es (embed t) = interp_E t`, where
  we only need handlers for `E` instead of for `Es`.
  If we happen to interp away all effects, using another theorem `interp_∅ t = t`.
-/
def embed [HasEff E Es] (t : ITree E A) : ITree Es A :=
  sorry

instance [HasEff E Es] : Coe (ITree E A) (ITree Es A) := ⟨embed⟩

-- theorem interp_embed [HasEff E Es] {t : ITree E A} {h : {A : Type} -> Es A -> ITree E A}
--   : interp h (embed (Es := Es) t) = interp h t
--   := sorry
