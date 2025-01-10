import ITree
import ITree.Spec.Theta

namespace LeanBoogie
open ITree

/- # ITree Specs Without Effects [DM4Ever]
  Without effects, if our tree diverges, we know that `spin` is the canonical representative of it,
  and for convergence it must be `.ret _`.
  With effects, this gets non-trivial, and we might have
-/
-- See section 4 of "Dijkstra Monads for ever".

-- Corresponding computation monad: `ITree Empty`.
abbrev ITree0 (A : Type) := ITree None A
@[aesop unfold 50%] def Converges (a : A) (t : ITree0 A) : Prop := t = .ret a
@[aesop unfold 50%] def Diverges (t : ITree0 A) : Prop := t = spin

/-- Source: https://lag47.github.io/assets/pdf/dissertation.pdf definition 9,
  and the Interaction Trees repo `PureITreeDijkstra.v` definition `monotonici`.  -/
@[aesop unfold 90%] def Monotonic (w : (p : ITree0 A -> Prop) -> Prop) : Prop :=
  (p1 p2 : ITree0 A -> Prop) ->
    (∀t : ITree0 A, p1 t -> p2 t) ->
      w p1 -> w p2

/-- Specification monad for eventless interaction trees. In the Dijkstra Monads for ever paper,
  this is called `DelaySpec`. We require the specification to adhere to some properties (mono, respeutt)
  but that is not very relevant for generating verification conditions.
  You should be able to pretend this is just `def ITree0W (A) := (ITree0 A -> Prop) -> Prop`. -/
def ITree0W (A : Type) := (w : (ITree0 A -> Prop) -> Prop) ×' Monotonic w

def ITree0W.pure {A   : Type} (a : A) : ITree0W A := ⟨
  fun (post : ITree None A -> Prop) => post (Pure.pure a),
  fun p1 p2 _ _ => by simp_all only⟩

def ITree0W.bind {A B : Type} (wa : ITree0W A) (wb : A -> ITree0W B) : ITree0W B := ⟨
  fun (post : ITree None B -> Prop) =>
    wa.1 (fun ta => (∃a:A, Converges a ta ∧ (wb a).1 post ) ∨ Diverges ta),
  by
    unfold Converges Diverges
    intro p1 p2 t h
    unfold ITree0W at wa wb
    obtain ⟨wa, wah⟩ := wa
    -- obtain ⟨wb, wbh⟩ := wb ?a
    simp only at *
    sorry
⟩

instance : Monad ITree0W where
  pure := .pure
  bind := .bind
instance : LawfulMonad ITree0W := sorry

def ITree0W.le (w1 w2 : ITree0W A) : Prop := ∀p, w2.1 p -> w1.1 p
instance : LE (ITree0W A) := ⟨ITree0W.le⟩

/-- DM4Ever section 4.3. -/
theorem ITree0W.bind_mono (wa₁ wa₂ : ITree0W A) (wb₁ wb₂ : A -> ITree0W B)
  (ha : wa₁ <= wa₂)
  (hb : ∀a, wb₁ a <= wb₂ a)
  : (wa₁ >>= wb₁) <= (wa₂ >>= wb₂)
  := fun post h => by
    dsimp [LE.le, le] at ha hb
    let ⟨wa₁, wa₁h⟩ := wa₁
    let ⟨wa₂, wa₂h⟩ := wa₂
    dsimp [Bind.bind, ITree0W.bind] at *
    unfold Monotonic at *
    sorry

-- ## Morphism θ from ITree0 to ITree0W

def ITree0.θ (t : ITree0 A) : ITree0W A := ⟨fun post => post t, by intro _ _ _ _; simp_all only⟩
instance : Theta ITree0 ITree0W := ⟨ITree0.θ⟩

theorem ITree0.θ_pure : θ (return a) = return a := rfl
theorem ITree0.θ_bind {a : ITree0 A} {b : A -> ITree0 B}
  : θ (a >>= b) = (θ a >>= fun a => θ (b a))
  := by
    dsimp [Bind.bind, ITree0W.bind, θ]
    -- ! This will be a substantial chunk of work, because you need to dig into coinduction
    sorry

instance instLawfulThetaITree0W : LawfulTheta ITree0 ITree0W := ⟨ITree0.θ_pure, ITree0.θ_bind⟩

theorem θ_if {t e : ITree0 A} [Decidable c] : θ (if c then t else e) = if c then θ t else θ e := by
  aesop



-- ## Specs for Iter

-- /-- From the Interaction Trees repo, `PureITreeDijkstra.v` definition `iterp`.
--   This is a convoluted coinductive definition in the Coq repo. -/
-- def ITree0W.iter (f : A -> ITree0W (A ⊕ B)) (a : A) : ITree0W B := ⟨
--   fun post hpost => sorry,
--   sorry
-- ⟩


-- set_option linter.unusedVariables false in
-- /-- Source: [DM4Ever] figure 4 `loop_invar_sound`, as well as in `DelaySpecMonad.v` definitino `loop_invar`. -/
-- theorem loop_invar (body : A -> ITree0 (A ⊕ B)) (a₀ : A)
--   (P : ITree0 B -> Prop)
--   (Inv : ITree0 (A ⊕ B) -> Prop)
--   (start : Inv (body a₀))
--   (step : ∀r, Inv r -> Inv (r >>= iter_lift body))
--   (stop : ∀t, Inv (t >>= fun b => return .inr b) -> P t)
--   : P (iter body a₀) ∨ Diverges (iter body a₀)
--   := trustITree "[DM4Ever] figure 4 `loop_invar_sound`, as well as in `DelaySpecMonad.v` definitino `loop_invar`"
