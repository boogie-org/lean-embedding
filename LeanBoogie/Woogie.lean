import LeanBoogie.Boogie
import LeanBoogie.Notation
import LeanBoogie.ITree.ITree0W

namespace LeanBoogie
open ITree

/-- This type doesn't support events on its `ITree`.
  See section 4.5 in DM4Ever.

  Reducing this type (with `S = BoogieState`), you get:
  ```
  S -> (ITree Empty (A × S) -> Prop) -> Prop
  ```
  Rearranging a little, you get the familiar predicate transformer type, from postc. to prec.:
  ```
  (ITree Empty (A × S) -> Prop) -> (S -> Prop)
  ```
  However, because `ITree0W` comes with some additional ballast such as monotonicity,
  it is a little uglier still:
  ```
  (BoogieState →
    (w : (p : ITree Empty (A × BoogieState) → Prop) -> RespEutt p → Prop) ×' Monotonic w)
  ```
-/
def Woogie : Type -> Type := StateT BoogieState ITree0W

example : Woogie A =
  (BoogieState →
    (w : (p : ITree Empty (A × BoogieState) → Prop) -> RespEutt p → Prop) ×' Monotonic w)
  := by rfl

def Woogie.mk
  (w : BoogieState -> (post : ITree0 (A × BoogieState) → Prop) -> RespEutt post → Prop)
  (w_mono : (s : BoogieState) -> Monotonic (w s))
  : Woogie A
  := fun s => ⟨w s, w_mono s⟩

/-- Very unsafe version of `Woogie.mk`, which just uses `sorry` to solve monotonicity. -/
def Woogie.mk!
  (w : BoogieState -> (post : ITree0 (A × BoogieState) → Prop) → Prop)
  : Woogie A
  := fun s => ⟨fun post _hpost => w s post, sorry⟩

def Woogie.pure (a : A) : Woogie A := fun s => return (a, s)
def Woogie.bind (a : Woogie A) (b : A -> Woogie B) : Woogie B := fun s => a s >>= fun a => b a.fst a.snd

instance : Monad Woogie where
  pure := .pure
  bind := .bind
instance : LawfulMonad Woogie := sorry

def Woogie.read (v : String) : Woogie Int :=
  fun (s:BoogieState) => ⟨
    fun (post) _ => post (.ret (s v, s)),
    by unfold Monotonic; aesop
  ⟩

def Woogie.write (v : String) (a : Int) : Woogie Unit :=
  fun s => ⟨
    fun post _ => post (.ret ((), s.update v a)),
    by rw [Monotonic]; aesop
  ⟩

/-- This is `θ_state` in DM4Ever. -/
def Boogie.θ (b : Boogie Empty A) : Woogie A :=
  fun s => ⟨
    fun post _ => post (b s),
    by rw [Monotonic]; aesop
  ⟩

instance : Theta (Boogie Empty) Woogie := ⟨Boogie.θ⟩

/-- Specification ordering [DM4Aall 3.1]. -/
def Woogie.le (w1 w2 : Woogie A) : Prop := ∀s p, (hp : RespEutt p) -> (w2 s).1 p hp -> (w1 s).1 p hp
instance : LE (Woogie A) := ⟨Woogie.le⟩

theorem Boogie.θ_pure : θ (return a) = (return a) := rfl
theorem Boogie.θ_bind {a : Boogie Empty A} {b : A -> Boogie Empty B}
  : θ (a >>= b) = (θ a >>= fun a => θ (b a))
  := by
    unfold θ
    dsimp [Bind.bind, StateT.bind.eq_unfold]
    unfold Woogie.bind
    funext s
    congr
    funext post hpost
    ext
    simp_all only [Prod.exists]
    constructor
    . intro h
      sorry
    . intro h
      cases h with
      | inl h =>
        have ⟨a1, s', converges, h2⟩ := h
        sorry
      | inr h_2 =>
        sorry

instance : LawfulTheta (Boogie Empty) (Woogie) := ⟨Boogie.θ_pure, Boogie.θ_bind⟩

theorem Boogie.θ_read : θ (Boogie.read v) = (Woogie.read v) := by sorry
theorem Boogie.θ_write : θ (Boogie.write v x) = (Woogie.write v x) := by sorry

theorem Boogie.θ_ite [Decidable φ]
  : θ (if φ then t else e)
  = (if φ then θ t else θ e)
  := by
  split
  next h => simp_all only
  next h => simp_all only

theorem Boogie.θ_ite' [Decidable φ]
  : θ (if φ then t else e)
  = Woogie.mk! (fun s post => (φ -> (θ t s).1 post sorry) ∧ (¬φ -> (θ e s).1 post sorry))
  := by
  split
  next h => simp_all only [true_implies, not_true_eq_false, false_implies, and_true]; rfl
  next h => simp_all only [false_implies, not_false_eq_true, true_implies, true_and]; rfl

def BoogV {A : Type} (w : Woogie A) (b : Boogie Empty A) : Prop := θ b <= w

theorem BoogV.ite [Decidable φ] {w : Woogie A}
  (tru :  φ -> BoogV w t)
  (fal : ¬φ -> BoogV w e)
  : BoogV w (if φ then t else e)
  := by aesop

theorem BoogV.ite' [Decidable φ] {w : Woogie A} {t e : Boogie Empty A}
  (tru :  φ -> θ t <= w)
  (fal : ¬φ -> θ e <= w)
  : θ (if φ then t else e) <= w
  := by aesop

theorem BoogV.ite'' [Decidable φ] {w : Woogie A}
  (tru :  φ -> t <= w)
  (fal : ¬φ -> e <= w)
  : (if φ then t else e) <= w
  := by aesop

-- * Thoughts on interp vs θ
-- `interp` is a monad morphism (from `ITree MemEv` to `StateT S (ITree Empty)` (aka Boogie))
-- `θ` is a monad morphism (from `StateT S (ITree Empty)` to `StateT S (ITreeSpec Empty)` (aka Woogie))
-- (1) ...so, you presumably can compose those two monad morphisms.
-- (2) ...can you go the other way, first apply `θ` and then `interp`?
