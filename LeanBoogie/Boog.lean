import Std
import Aesop
import LeanBoogie.ITree
import LeanBoogie.Notation
import LeanBoogie.Iter

namespace Boogie

open Std (HashSet HashMap)

/-
  # Boogie state monad
  Tracks values of boogie variables during execution.
-/


/-- Assigns values to every variable. Ideally you'd want `(v : String) -> v ∈ ValidVars -> Int`. -/
abbrev BoogieState := String -> Int

def BoogieState.update (v : String) (val : Int) : BoogieState -> BoogieState :=
  fun σ v' => if _h : v' = v then val else σ v'
instance : EmptyCollection BoogieState := ⟨fun _ => 0⟩


/-- State monad during execution of boogie programs. Assigns values to every variable. -/
abbrev Boog (E : Type) : Type -> Type := StateT BoogieState (ITree E)

def Boog.read (v : String) : Boog E Int := fun σ => pure (σ v, σ)
def Boog.write (v : String) (val : Int) : Boog E Unit := fun σ => pure ((), BoogieState.update v val σ)
/-- Apply a pure function to a variable. Useful for simple operations such as increments, setting to zero, etc. -/
def Boog.update (v : String) (f : Int -> Int) : Boog E Unit
  := Boog.read v >>= fun x => Boog.write v (f x)


/- ## Helpers for writing imperative programs.  -/

def Boog.iter (f : A -> Boog E (A ⊕ B)) : A -> Boog E B := sorry
instance : Iter (Boog E) := ⟨Boog.iter⟩

def Boog.skip : Boog E Unit := pure ()
def Boog.seq (a b : Boog E Unit) : Boog E Unit := a >>= (fun () => b)
instance : Seqi (Boog E Unit) := ⟨Boog.seq⟩

def Boog.case (t e : Boog E A) : Bool -> Boog E A
| true => t
| false => e

def Boog.ite (c : Boog E Bool) (t e : Boog E A) : Boog E A :=
  c >>= Boog.case t e

abbrev Boog.pure : A -> Boog E A := Pure.pure
abbrev Boog.bind : (Boog E A) -> (A -> Boog E B) -> Boog E B := Bind.bind

/-- Actually execute a boogie program, starting with every variable being 0-initialized. -/
def Boog.run (m : Boog Empty Unit) (fuel : Nat) : Option BoogieState :=
  let s₀ : BoogieState := (fun _ => 0)
  let stuff := StateT.run m s₀
  let ⟨_, ret⟩ := ITree.run stuff Empty.elim fuel
  ret.map Prod.snd

/-- Equivalence up-to-tau, but adapted for the `Boog` monad. -/
def EuttB (b1 : Boog E A) (b2 : Boog E A) : Prop := ∀σ : BoogieState, Eutt (b1 σ) (b2 σ)
infixr:20 " ~=~ " => EuttB

axiom EuttB.eq {E A : Type} {x y : Boog E A} : EuttB x y -> x = y

theorem Boog.ite_push_state [Decidable c] {t e : Boog E A}
  : (if c then t else e) σ ~~ (if c then t σ else e σ)
  := by split; repeat exact Eutt.refl _

theorem Boog.bind_push_state {a : Boog E A} {b : A -> Boog E B}
  : (a >>= b) σ ~~ (a σ >>= fun res => b res.fst res.snd)
  := sorry

def Boog.while_ (c : Boog E Bool) (body : Boog E Unit) : Boog E Unit :=
  Boog.iter
    (fun () => Boog.ite c
      (do body; return .inl ())
      (return .inr ()))
    ()

@[simp] theorem ite_bind [Monad m] [Decidable c] {m1 m2 : m a} {k : a -> m b}
  : (if c then m1       else m2      ) >>= k
  =  if c then m1 >>= k else m2 >>= k
  := by aesop
