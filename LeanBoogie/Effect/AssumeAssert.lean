import ITree
import ITree.Spec.ITree0W

namespace LeanBoogie
open ITree

/-
  # `Assume` and `Assert` Effect
  Allows you to obtain proofs of arbitrary propositions, even `False`.
  It is up to whoever interprets the event to provide the actual proof.
  ```
  .vis (Mem.rd "i") fun (i : Int) =>
    .vis (AmAt.am (i < 123)) fun ⟨(prf : i < 2)⟩ =>
      ...
  ```

  Look at `Examples/NonDeterminism/AmAtChoice.lean` for examples.

  ## Interpreting
  When you encounter `ITree.vis (.am P) k`, with `k : P -> ITree _ A`, you need to provide a proof
  of `P` in order to obtain the rest of the ITree. You can do this by either:
  1. Finding a proof of `P`. Let's say `P = (x < 3)`. Let's say you are symbolically executing your
     stateful program and thus actually know the concrete value of `x` at this point.
     Then you can decide this proposition and provide the proof and obtain the continuation.
  2. Ignoring the assumption altogether, either by `sorry` or `implemented_by`. This could be useful
     when you want to obtain executable code and no longer care about `assume`.
  3. When computing *verification conditions*, interpreting into a Dijkstra monad.
     Assumptions become implication `(prf : P) -> computeVC (k prf)`, and
     assertions become conjunction `(prf : P) × computeVC (k prf)`.
     Dijkstra monads are slightly different (i.e. predicate transformers), but the intuition still
     holds.

-/

/-- Effect for `assume` and `assert`. Refer to the doc comment in `AssumeAssert.lean` for more info. -/
inductive AmAt : Type -> Type
/-- Assume `P`. -/
| am : (P : Prop) -> AmAt (PLift P)
/-- Assert `P`. -/
| at : (P : Prop) -> AmAt (PLift P)

def assume' [SubEff AmAt Es] (P : Prop) : ITree Es (PLift P) := ITree.trigger (AmAt.am P)

abbrev assume [SubEff AmAt Es] (P : Prop) : ITree Es Unit := do
  let _ <- assume' P

def assert' [SubEff AmAt Es] (P : Prop) : ITree Es (PLift P) := ITree.trigger (AmAt.at P)

abbrev assert [SubEff AmAt Es] (P : Prop) : ITree Es Unit := do
  let _ <- assert' P

/-- This is sound! You can have `ITree E False`, but never `False`.
  This does not spin either, it just asks for the return value (a `False`) from the world.
  Which the world can not give, unless the world itself introduces an assumption of `False`,
  as we (intend to) do when interpreting into the Dijkstra monad `ITreeW`. -/
def ohno [SubEff AmAt E] : ITree E Empty := do
  let .up prf <- assume' False
  prf.elim

/-- Handler of `AmAt` into the eventless ITree Dijkstra monad.
  `θ (ITree.vis (.am φ) k)` = `(prf : φ) -> θ (k prf)`
  `θ (ITree.vis (.at φ) k)` = `(prf : φ) × θ (k prf)`

  This is similar to `interp`, but `interp` is not enough, since an event handler is local to
  just the event, but we need to have the continuation `k` when we interpret.
-/
def AmAt.θ : ITree AmAt A -> ITree0W A := sorry

/-- Intuitively `θ (ITree.vis (.am φ) k)` = `(prf : φ) -> θ (k prf)` -/
theorem AmAt.θ_am {k : _ -> ITree AmAt A}
  : θ (ITree.vis (.am φ) k)
  -- = ⟨fun Post => (prf : φ) -> (θ (k ⟨prf⟩)).1 Post,
  = ⟨fun Post =>
      (prf : φ) ->
        let ⟨t, tm⟩ := θ (k ⟨prf⟩)
        t Post,
    by intro; sorry⟩
  := sorry

-- Lean doesn't seem to have this somehow?
structure AndD (α : Prop) (β : α -> Prop) : Prop where
  left : α
  right : β left

theorem AmAt.θ_at {k : _ -> ITree AmAt A}
  : θ (ITree.vis (.at φ) k)
  = ⟨fun Post =>
      AndD φ fun prf =>
        let ⟨t, tm⟩ := θ (k ⟨prf⟩)
        t Post,
    by
      intro t1 t2 h o
      sorry
    ⟩
  := sorry
