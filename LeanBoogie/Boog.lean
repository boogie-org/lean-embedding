import Std
import Aesop

open Std (HashSet HashMap)

/-
  # Boogie state monad
  Tracks values of boogie variables during execution.
-/

/-- Assigns values to every variable. Ideally you'd want `(v : String) -> v ∈ ValidVars -> Int`. -/
abbrev BoogieState := String -> Int

/-- State monad during execution of boogie programs. Assigns values to every variable. -/
abbrev Boog : Type -> Type := StateM BoogieState

def Boog.skip : Boog Unit := pure ()
def Boog.seq (a b : Boog Unit) : Boog Unit := a >>= (fun _ => b)

def Boog.get (v : String) : Boog Int := do return (<- getThe BoogieState) v
def Boog.set (v : String) (e : Boog Int) : Boog Unit := do
  let val <- e
  modifyThe BoogieState
      (fun f x => if x = v then val else f x)

#check ite

/-- This is a little ugly, because lean `if` actually takes a (decidable) `Prop`, not a `Bool` -/
def Boog.ifthenelse (c : Boog Bool) (t e : Boog Unit) : Boog Unit := do
  if <- c then t else e

def Boog.ifthen (c : Boog Bool) (t : Boog Unit) : Boog Unit := do
  if <- c then t

/-- Actually execute a boogie program, starting with every variable being 0-initialized. -/
def runBoogie (m : Boog Unit) : BoogieState :=
  let s₀ : BoogieState := (fun _ => 0)
  let ((), s') := StateT.run m s₀
  s'

/-
  ## Helper lemmas
  Elaborated Boogie programs are quite noisy, and not structured in a way that Lean-Auto can deal
  with very well. So here we define a bunch of lemmas which (hopefully) bring elaborated Boogie
  programs into a shape that SMT solvers can deal with.
-/

theorem bind_eq2 (a: Boog A) (b: A -> Boog B) : (a >>= b : Boog B) = fun s => let x := a s ; b x.fst x.snd
:= by
  unfold bind Monad.toBind StateT.instMonad StateT.bind
  simp

@[aesop unsafe] theorem one_var {t1 t2 : String -> Int} (x : String)
  (h_x     : t1 x = t2 x)
  (h_other : (∀v, ¬ v = x -> t1 v = t2 v))
  : ∀v, t1 v = t2 v
  := by intro v; if h : x = v then exact h ▸ h_x else aesop

@[simp]
theorem ite_bind:
  ∀ [Monad m]
    [LawfulMonad m]
    {c : Bool}
    {m1 m2 : m a}
    {k : a -> m b},
   (if c then m1       else m2      ) >>= k
  = if c then m1 >>= k else m2 >>= k
  := by aesop

@[simp]
theorem var_congr_ite
  [Decidable c]
  (x : String)
  {t e t' e' : Boog A}
  (h_t :   c -> (t st).2 x = (t' st).2 x)
  (h_e : ¬ c -> (e st).2 x = (e' st).2 x)
  : ((if c then t else e) st).2 x = ((if c then t' else e') st).2 x
  := by aesop

@[simp]
theorem state_congr_ite [Decidable c] {t e : Boog A}
  : (if c then t else e) st = (if c then t st else e st)
  := by aesop

@[simp]
theorem state_proj_congr_ite [Decidable c] {tst est :(A × S)}
  : (if c then tst else est).2 = (if c then (tst).2 else (est).2)
  := by aesop

@[simp]
theorem state_var_ite_congr [Decidable c] {t e : String -> Int}
  : (if c then t else e) v = (if c then t v else e v)
  := by aesop
