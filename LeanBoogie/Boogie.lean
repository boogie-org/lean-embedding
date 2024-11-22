import Std
import Aesop
import LeanBoogie.ITree
import LeanBoogie.Notation
import LeanBoogie.Iter

namespace LeanBoogie

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
abbrev Boogie (E : Type) : Type -> Type := StateT BoogieState (ITree E)

def Boogie.read (v : String) : Boogie E Int := fun σ => pure (σ v, σ)
def Boogie.write (v : String) (val : Int) : Boogie E Unit := fun σ => pure ((), BoogieState.update v val σ)
/-- Apply a pure function to a variable. Useful for simple operations such as increments, setting to zero, etc. -/
def Boogie.update (v : String) (f : Int -> Int) : Boogie E Unit
  := Boogie.read v >>= fun x => Boogie.write v (f x)


/- ## Helpers for writing imperative programs.  -/

def Boogie.iter (f : A -> Boogie E (A ⊕ B)) : A -> Boogie E B := sorry
instance : Iter (Boogie E) := ⟨Boogie.iter⟩

def Boogie.skip : Boogie E Unit := pure ()
def Boogie.seq (a b : Boogie E Unit) : Boogie E Unit := a >>= (fun () => b)
instance : Seqi (Boogie E Unit) := ⟨Boogie.seq⟩

def Boogie.case (t e : Boogie E A) : Bool -> Boogie E A
| true => t
| false => e

def Boogie.ite (c : Boogie E Bool) (t e : Boogie E A) : Boogie E A :=
  c >>= Boogie.case t e

abbrev Boogie.pure : A -> Boogie E A := Pure.pure
abbrev Boogie.bind : (Boogie E A) -> (A -> Boogie E B) -> Boogie E B := Bind.bind

/-- Actually execute a boogie program, starting with every variable being 0-initialized. -/
def Boogie.run (m : Boogie Empty Unit) (fuel : Nat) : Option BoogieState :=
  let s₀ : BoogieState := (fun _ => 0)
  let stuff := StateT.run m s₀
  let ⟨_, ret⟩ := ITree.run stuff Empty.elim fuel
  ret.map Prod.snd

/-- Equivalence up-to-tau, but adapted for the `Boogie` monad. -/
def EuttB (b1 : Boogie E A) (b2 : Boogie E A) : Prop := ∀σ : BoogieState, Eutt (b1 σ) (b2 σ)
infixr:20 " ~=~ " => EuttB

axiom EuttB.eq {E A : Type} {x y : Boogie E A} : EuttB x y -> x = y

theorem Boogie.ite_push_state [Decidable c] {t e : Boogie E A}
  : (if c then t else e) σ ~~ (if c then t σ else e σ)
  := by split; repeat exact Eutt.refl _

theorem Boogie.bind_push_state {a : Boogie E A} {b : A -> Boogie E B}
  : (a >>= b) σ ~~ (a σ >>= fun res => b res.fst res.snd)
  := sorry

def Boogie.while_ (c : Boogie E Bool) (body : Boogie E Unit) : Boogie E Unit :=
  Boogie.iter
    (fun () => Boogie.ite c
      (do body; return .inl ())
      (return .inr ()))
    ()

@[simp] theorem ite_bind [Monad m] [Decidable c] {m1 m2 : m a} {k : a -> m b}
  : (if c then m1       else m2      ) >>= k
  =  if c then m1 >>= k else m2 >>= k
  := by aesop
