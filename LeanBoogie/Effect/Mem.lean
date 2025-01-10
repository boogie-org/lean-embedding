import ITree
import LeanBoogie.ConTy
import Mathlib.Data.Real.Basic

namespace LeanBoogie
open ITree (SubEff trigger Handler None)

/-
  # Memory (Effects) in Boogie

  Without interpretation yet. For that, look into `State.lean`.
-/

-- ## `Mem` Effect

inductive Mem (Γ : Con) : Type -> Type where
| rd : Var Γ A          -> Mem Γ A
| wr : Var Γ A -> TyA A -> Mem Γ Unit
-- /-- Simultaneously swap two variables. -/
-- | swap : Var Γ A -> Var Γ A -> Mem Γ Unit

def Mem.read  (v : Var Γ A)           : ITree (Mem Γ) A    := trigger (.rd v)
def Mem.write (v : Var Γ A) (val : A) : ITree (Mem Γ) Unit := trigger (.wr v val)

/-- Apply a pure function to a variable. E.g. `Mem.update x (· + 10)`. -/
abbrev Mem.update (v : Var Γ A) (f : A -> A) : ITree (Mem Γ) Unit := do
  let val <- read v
  write v (f val)

-- def Mem.merge : ITree (Mem Γ & Mem Δ) A -> ITree (Mem (Γ ++ Δ)) A := sorry

def Mem.split : Mem (Γ ++ Δ) A -> (Mem Γ & Mem Δ) A
| .rd v => match v.split with
  | .inl v => .left (.rd v)
  | .inr v => .right (.rd v)
| .wr v val => match v.split with
  | .inl v => .left (.wr v val)
  | .inr v => .right (.wr v val)

instance : SubEff (Mem (Γ ++ Δ)) (Mem Γ & Mem Δ) where
  injEv := Mem.split

instance : SubEff (Mem []) None where injEv e := nomatch e
instance : SubEff (Mem []) ∅ where injEv e := nomatch e
instance : SubEff (Mem []) 0 where injEv e := nomatch e

private def Γ : Con := [.int, .bv 32, .bool ~> .int]
private def i : Var Γ .int := .v0
private def b : Var Γ (.bv32) := .v1
private def f : Var Γ (.bool ~> .int) := .v2
private example : ITree (Mem Γ) Unit := do
  let fn : Bool -> Int <- Mem.read f
  Mem.write b (fn false)
