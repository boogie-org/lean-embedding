import LeanBoogie.Notation

namespace LeanBoogie

def case [Monad M] (ca : A -> M C) (cb : B -> M C) (ab : M (A ⊕ B)) : M C := do
  match <- ab with
  | .inl a => ca a
  | .inr b => cb b

/-
  # `Iter`ative monads
  This does not mention `ITree`s, but we can state some properties nonetheles.
-/

/-- The monad `M` is equipped with `iter`.

  Implementing this typeclass automatically gives you a few other goodies, such as `loop`, `While`.
 -/
class Iter (M : Type u -> Type v) extends Monad M where
  /-- Repeat `f` until it returns `B`. -/
  iter : {A B : Type u} -> (f : A -> M (A ⊕ B)) -> (a₀ : A) -> M B
  -- iterLift : ... := ...
  -- loop : ... := ...
  -- While : ... := ...

export Iter (iter)

def iterLift [Iter M] (body : A -> M (A ⊕ B)) : (A ⊕ B) -> M (A ⊕ B)
| .inl a => body a
| .inr b => return .inr b

/-- `iterOn a₀ f = iter f a₀`. -/
abbrev iterOn [Iter M] {A B : Type u} (a₀ : A) (f : A -> M (A ⊕ B)) :=
  iter f a₀

/-- A different phrasing of `iter`.

  From the ITree paper:
  ```
  Definition loop (body : C + A → itree E (C + B)) : A → itree E B :=
    fun a ⇒ iter (fun ca ⇒
      cb <- body ca ;;
      match cb with
      | inl c ⇒ Ret (inl (inl c))
      | inr b ⇒ Ret (inr b)
      end) (inr a).
  ```
-/
def loop [Iter M] (body : C ⊕ A -> M (C ⊕ B)) (a : A) : M B :=
  sorry

-- Maybe use this instead of `Bool` in `While`?
-- structure DProp : Type u where
--   P : Prop
--   decide : Decidable P

/-- Combinator for writing `while` loops, expressed in terms of `iter`.

  Uppercase because `while` is a keyword in Lean. -/
def While [Iter M] (c : M Bool) (body : M Unit) : M Unit :=
  iter (fun () => do
    if (<- c) then
      body
      return .inl ()
    else
      return .inr ()
  )
  ()

class LawfulIter (M : Type /- u -/ -> Type v) [Iter M] : Prop where
  iter_fp' {f : A -> M (A ⊕ B)} {a₀ : A}
    : iter f a₀
    = do
      match <- f a₀ with
      | .inl a => iter f a
      | .inr b => return b
  while_fp {c : M Bool} : While c body = do if (<- c) then body; While c body
  /-- Unroll `iter` once. Note that the first case is `(fun a => iter f a)` instead of `iter f`,
    so that we can apply `iter_fp` multiple times. -/
  iter_fp {f : A -> M (A ⊕ B)} {a₀ : A} : iter f a₀ = case (fun a => iter f a) pure (f a₀) := iter_fp'
  iter_fp'' {f : A -> M (A ⊕ B)} : iter f = fun a₀ => case (iter f) pure (f a₀) := funext (fun a => iter_fp (a₀ := a))

export LawfulIter (iter_fp iter_fp' iter_fp'' while_fp)

-- /-- We can unroll `iter f`. -/
-- theorem iter_fp {f : KTree E A (A ⊕ B)} : iter f ~~~ f >>> case (iter f) id := trustITree "page 9"
-- theorem iter_fp_nonK {f : KTree E A (A ⊕ B)} : iter f p ~~ f p >>= case (iter f) id := by sorry
-- theorem iter_comp : iter (f >>> case g inr) ~~~ f >>> case (iter (g >>> case f inr)) id := trustITree "page 9"
-- /-- "Iterating f to completion, then executing g" is equivalent to iterationg "execute f, and if it wanted to complete, execute g" to completion. -/
-- theorem iter_param {f : KTree E A (A ⊕ B)} {g : KTree E B C} : iter f >>> g ~~~ iter (f >>> bimap id g) := trustITree "page 9"
