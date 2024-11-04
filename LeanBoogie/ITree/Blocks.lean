import LeanBoogie.ITree.ITree
import LeanBoogie.ITree.Eutt
import LeanBoogie.ITree.Monad
import LeanBoogie.ITree.Mem
import LeanBoogie.Boog

namespace Boogie

/-
  # Basic, Labels, `goto`
-/

/-- A block is just an ITree which tells us which next block(s) to jump to.
  - If returned jump list is empty: This cfg (which is usually a procedure) is done, i.e. `return;`.
  - If returned jump list has two or more elems: Non-deterministic jump.
    Currently not supported, and we just pick the first label for now, but eventually we'll
    implement an oracle to choose the jump label via ITree events. -/
abbrev Block /- (nBlocks : Nat) (Γ : Vars) -/ : Type
  := ITree (MemEv /- Γ -/) (List Nat)

/-- Control flow graph. Just a bunch of blocks. -/
structure Cfg : Type where
  /-- Which Boogie variables we have. Later: Also store their types. -/
  vars : List Unit := []
  blocks : List (Block /- vars -/)
  -- entry : Fin blocks.length := by exact ⟨0, by rw [List.length]; omega⟩
  entry : Nat := 0

-- ## Example:

def bb0 : Block := do
  let i0 <- Mem.get "i0"
  Mem.set "i1" (i0 == 0).toNat
  return [1, 2]

def bb1 : Block := do
  let i1 <- Mem.get "i1"
  ITree.assume (i1 = 0)
  return [4]

def myCfg : Cfg := {
  vars := []
  blocks := [bb0, bb1]
}



-- // Reminder: def iter (body : A -> ITree E (Sum A B)) (a : A) : ITree E B
-- Reminder: def loop (body : Sum C A -> ITree E (Sum C B)) (a : A) : ITree E B
/-- Run a bunch of blocks until no jump label is returned anymore.
  ```lean4
  let mut l : Label := 0 -- or cfg.entry

  -- Then repeat this:
  let ls : List Label <- cfg.blocks[l] -- run block
  if ls.length = 0
    then return
    else l := choose lbls
  ```
-/
def Cfg.run (cfg : Cfg) : ITree MemEv Unit :=
  ITree.iter (A := Nat) (B := Unit) (fun a => do
    let lbls <- cfg.blocks[a]! -- run block -- ! Panic if label is invalid
    if h : ¬ lbls.length = 0 then
      return .inl lbls[0]
    else
      return .inr () -- we are done
  )
  cfg.entry
