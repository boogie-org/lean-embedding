import LeanBoogie.ITree
import LeanBoogie.Effect.AssumeAssert

namespace LeanBoogie
open ITree (HasEff)

/-
  # Nondeterministic Choice
  This is just a temporary solution, and we should probably use choice trees instead.
  Choice trees are not too dissimiliar from the following approach, however.
-/

inductive Choice : Type -> Type where
| ch : (A : Type) -> Choice A

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
