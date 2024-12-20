import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Iter
import LeanBoogie.Notation.Iter

namespace ITree

/-
  # Effects
-/

/-- No effects. This is essentially `Empty`. -/
def None : Type -> Type := fun _ => PEmpty
@[reducible] instance : EmptyCollection (Type -> Type) := ⟨None⟩
@[reducible] instance : OfNat (Type -> Type) 0 where ofNat := None

/-- The union of two event types. -/
inductive EffProd (E F : Type -> Type) : Type -> Type
| left  : E A -> EffProd E F A
| right : F A -> EffProd E F A
infixl:60 " & " => EffProd

def EffNProd (Es : List (Type -> Type)) : (Type -> Type) :=
  fun Ans => (i : Fin Es.length) -> Es[i] Ans


/-- Asserts that the collection of events `F` has event `E`.

  Note: Usage of this typeclass in conjunction with `Effect.Prod` seems a little buggy, I haven't
  gotten around to why it is wonky yet.
-/
class HasEff (E : semiOutParam (Type -> Type)) (F : Type -> Type) where
  inj : {A : Type} -> E A -> F A
  -- /-- The rest of the events in `Es`, without `E`. -/
  -- Strip : Type -> Type
  -- elim : {A : Type} -> {motive : Type} -> (E A -> motive) -> (Strip A -> motive) -> F A -> motive

variable {E F G : Type -> Type}
variable {A : Type}

instance instCoeEff [HasEff E F] : Coe (E A) (F A)
  := ⟨HasEff.inj⟩
attribute [coe] HasEff.inj

instance (priority := low) instHasEff_id : HasEff E E where
  inj := id
  -- Strip := None
  -- elim l _ := l

instance instHasEff_left : HasEff E (E & F) where
  inj := .left
  -- Strip := F
  -- elim l r := fun | .left e1 => l e1 | .right e2 => r e2

instance instHasEff_right : HasEff F (E & F) where
  inj := .right
  -- Strip := E
  -- elim l r := fun | .left e1 => r e1 | .right e2 => l e2


/-
  # Interp, Handlers
  The ITree paper just defines one `interp` using `iter`, for which you can then obtain concrete
  interpretations by giving it a `h`andler.

  I think it might be worthwhile to define handlers as going into monad transformers instead of monads:
  ```
  def HandlerT (E : Type -> Type) (T : (Type -> Type u) -> Type -> Type u) : Type _ :=
    {M : Type -> Type u} -> {A : Type} -> E A -> T M A
  ```
  This might make composing handlers easier. For example, you could define *one* handler for
  interpreting memory events, which results in `StateT (ConA Γ)`, instead of having a whole family
  of handlers for every `M`, resulting in `StateT (ConA Γ) M`.
-/

variable {M : Type -> Type u} [Monad M] [Iter M]

/-- Handles events `E` by interpreting them into the output monad `M`.
  For example, `Handler (Mem Γ) (StateT ..)` -/
def Handler (E : Type -> Type) (M : Type -> Type u) : Type _ :=
  ⦃A : Type⦄ -> E A -> M A

-- def HandlerT (E : Type -> Type) (T : (Type -> Type u) -> Type -> Type u) : Type _ :=
--   {M : Type -> Type u} -> ⦃A : Type⦄ -> E A -> T M A

/-- Interpreting events into another monad, which may again be the ITree monad but with e.g.
  fewer or different effects. -/
def interp [Monad M] [Iter M] (h : Handler E M) : ITree E A -> M A :=
  -- Iter.iter (A := ITree E A) (B := ULift A) <|
  --   ITree.cases (E:=E) (A:=A) (motive := fun _ => ITree E ((ITree E A) ⊕ A)) -- ! Need universe-polymorphic ITrees for this. Alternatively, maybe a direct definition of `interp` with `corec`, without relying on `iter` will suffice?
  --     (fun (a : A) => return Sum.inr a)
  --     (fun t => return Sum.inl t)
  --     (fun e k => h e >>= fun ans => return Sum.inl (k ans))
  sorry


/-
  ## Collection of common `Handler`s
  Figure 10 in the ITree paper.
-/

def Handler.id : Handler E (ITree E) := fun _ => trigger
def Handler.inj [HasEff E F] : Handler E (ITree F) := fun _ e => trigger (HasEff.inj e)

-- def Handler.left :
def Handler.inl : Handler E (ITree (E & F)) := fun _ e => trigger (.left e)
def Handler.inr : Handler F (ITree (E & F)) := fun _ e => trigger (.right e)
def Handler.case (he : Handler E M) (hf : Handler F M) : Handler (E & F) M := fun _ e =>
  match e with
  | .left e => he e
  | .right f => hf f

def Handler.comp (f : Handler E (ITree F)) (g : Handler F (ITree G)) : Handler E (ITree G) :=
  fun _ e => interp g (f e)


variable {h : Handler E M}

@[simp] theorem interp_pure : interp h (return a : ITree E A) = return a := by
  sorry

@[simp] theorem interp_trigger : interp h (trigger e) = h e := by
  sorry

@[aesop unsafe 1%]
theorem interp_bind : interp h (a >>= b) = (interp h a) >>= (fun a => interp h (b a)) := by
  sorry

theorem interp_iter {f : A → ITree E (A ⊕ B) } : interp h (Iter.iter f a) = Iter.iter (fun a => interp h (f a)) a := by
  sorry

@[aesop unsafe 1%]
theorem interp_ite [Decidable φ] : interp h (if φ then t else e) = (if φ then interp h t else interp h e) := by
  split <;> simp_all only

-- theorem interp_left (t : ITree (E & F) A) : interp (Handler.left h) t = sorry := sorry
/-
  ## Embedding
-/

/-- We can embed an ITree with fewer effects into an ITree with more.

  *TODO*: We should have the following theorem: `interp_Es (embed t) = interp_E t`, where
  we only need handlers for `E` instead of for `Es`.
  If we happen to interp away all effects, using another theorem `interp_∅ t = t`.
-/
def embed [HasEff E F] : ITree E A -> ITree F A := interp Handler.inj

instance [HasEff E F] : Coe (ITree E A) (ITree F A) := ⟨embed⟩


#check Multiset
