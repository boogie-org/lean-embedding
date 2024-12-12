import LeanBoogie.ITree
import LeanBoogie.ConTy
import Mathlib.Data.Real.Basic

namespace LeanBoogie
open ITree (HasEff)

/-
  # Memory (Effects) in Boogie

  Without interpretation yet. For that, look into `State.lean`.
-/

-- ## `Mem` Effect

inductive Mem (Γ : Con) : Type -> Type where
| rd : Var Γ A          -> Mem Γ A
| wr : Var Γ A -> TyA A -> Mem Γ Unit

def Mem.read  (v : Var Γ A)           : ITree (Mem Γ) A    := .vis (.rd v    ) .ret
def Mem.write (v : Var Γ A) (val : A) : ITree (Mem Γ) Unit := .vis (.wr v val) .ret
/-- Apply a pure function to a variable. E.g. `Mem.update x (· + 10)`. -/
abbrev Mem.update (v : Var Γ A) (f : A -> A) : ITree (Mem Γ) Unit := do
  let val <- read v
  write v (f val)

def Mem.read'  (v : Var Γ A)           : ITree (E & Mem Γ) A    := .vis (Mem.rd v    ) .ret
def Mem.write' (v : Var Γ A) (val : A) : ITree (E & Mem Γ) Unit := .vis (Mem.wr v val) .ret

-- the most general form is like this, with `HasEff`:
def Mem.read''  [HasEff (Mem Γ) E] (v : Var Γ A)           : ITree E A    := .vis (Mem.rd v    ) .ret
def Mem.write'' [HasEff (Mem Γ) E] (v : Var Γ A) (val : A) : ITree E Unit := .vis (Mem.wr v val) .ret

private def Γ : Con := [.int, .bv 32, .bool ~> .int]
private def i : Var Γ .int := .v0
private def b : Var Γ (.bv32) := .v1
private def f : Var Γ (.bool ~> .int) := .v2
private example : ITree (Mem Γ) Unit := do
  let fn : Bool -> Int <- Mem.read f
  Mem.write b (fn false)

def merge : ITree (Mem Γ & Mem Δ) A -> ITree (Mem (Γ ++ Δ)) A := sorry


/-
  # The Boogie Way
-/

axiom Ref : Type
def C.data : Ref -> Int := sorry
def C.next : Ref -> Ref := sorry
def alloc : Ref -> Prop := sorry -- which refs are allocated
