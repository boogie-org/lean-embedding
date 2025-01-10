import ITree
import ITree.Spec.ITree0W
import LeanBoogie.Effect.AssumeAssert

namespace LeanBoogie
open ITree

/-
  # Nondeterministic Choice
  We can ask the world for some arbitrary value of some type, such as `Bool`, or `Fin _`.
  The cardinality of this type is the amount of branches we get.
  We use this for non-det jumps between blocks in Boogie.

  See `Examples/AmAtChoice.lean`.

  ## Interpreting
  1. The world gives you a value, i.e. an oracle.
  2. When generating *verification conditions*: Let's say your target monad intuitively describes a
     set of programs, which e.g. a Dijkstra monad does.
     The program `let c <- choice Bool; p` can be interpreted into a set of two programs.
     We want the following to hold: `θ (ITree.vis (.ch C) k)` = `∀c:C, θ (k c)`
-/

/-- Non-deterministic choice. -/
inductive Choice : Type -> Type where
| ch : (A : Type) -> Choice A

/-- Non-deterministic choice. -/
def choice (A : Type) : ITree Choice A := .vis (Choice.ch A) .ret

/-- `if` implemented via nondeterministic choice and assumes/asserts.
  Note: No more `[Decidable φ]`. -/
def iteNondet (φ : Prop) (t e : ITree (Choice & AmAt) A) : ITree (Choice & AmAt) A :=
  .vis (Choice.ch Bool) fun
    | true  => .vis (.right <| AmAt.am    φ ) (fun ⟨_h⟩ => t)
    | false => .vis (.right <| AmAt.am (¬ φ)) (fun ⟨_h⟩ => e)

/-- `if` implemented via nondeterministic choice and assumes/asserts.
  Note: No more `[Decidable φ]`. -/
def diteNondet (φ : Prop)
  (t : φ -> ITree (Choice & AmAt) A)
  (e : ¬ φ -> ITree (Choice & AmAt) A)
  : ITree (Choice & AmAt) A :=
  .vis (Choice.ch Bool) fun
    | true  => .vis (.right <| AmAt.am    φ ) (fun ⟨h⟩ => t h)
    | false => .vis (.right <| AmAt.am (¬ φ)) (fun ⟨h⟩ => e h)

def Choice.θ : ITree Choice A -> ITree0W A := sorry

/-- Handler of `Choice` events into the eventless ITree Dijkstra monad.
  `θ (ITree.vis (.ch C) k)` = `∀c:C, θ (k c)` -/
theorem Choice.θ_ch {k : _ -> ITree Choice A}
  : θ (ITree.vis (.ch C) k)
  = ⟨fun Post => ∀c : C, (θ (k c)).1 Post,
    by sorry⟩
  := sorry
