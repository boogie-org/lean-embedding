import LeanBoogie.ITree
import LeanBoogie.Boog

namespace Boogie

open ITree KTree

/-
  # Basic, Labels, `goto`
-/

abbrev Label := Nat
abbrev Labels := { xs : List Label // xs.length >= 0 }

structure Block : Type where
  assumes : ITree MemEv Bool := ITree.ret true
  /-- A block is code which returns at least one label to jump to. -/
  code : ITree MemEv Labels

/-- Boogie procedure. Just a bunch of blocks. -/
structure Procedure : Type where
  blocks : List Block

/-- Get a block, or spin forever if index is invalid. -/
def getBlock (proc : Procedure) (l : Label) : ITree E Block := do
  if h : l < proc.blocks.length then return proc.blocks[l]
  else ITree.spin

/-- Return the label of the first block whose `assume`s decide to true. If none are, spin. -/
def choose (proc : Procedure) : KTree MemEv Labels Label
  := fun ⟨ls, _⟩ => impl proc ls
where impl (proc : Procedure) : KTree MemEv (List Label) Label
| [] => ITree.spin
| l :: ls => do
  let b <- getBlock proc l
  if <- b.assumes
    then return l
    else impl proc ls

#check case

/-- Run a bunch of blocks until no jump label is returned anymore. -/
-- def Procedure.run (proc : Procedure) : Label -> ITree MemEv Unit :=
def Procedure.run (proc : Procedure) : KTree MemEv Label Unit :=
  ITree.iter (A := Label) (B := _) fun (l : Label) => do
    let block <- getBlock proc l
    let ls : Labels <- block.code -- run block
    -- TODO: potentially non-deterministic branching.
    let l <- choose proc ls
    if l = 0 then return .inr () -- hard-code label 0 as the exit label for now.
    else return .inl l
    /- Here, `run` must somehow know which of the labels to jump to, because we are essentially
      building an interpreter, and Lean is deterministic. So how can we know this?
      1. Sometimes, the `assume`s at the beginning of each block are disjoint, so the jump is
        actually deterministic. The problems with this are:
        - We'd need to *look inside* those blocks. We have the list of blocks in `proc`, but they
          are of type `ITree _ _`, which we can't pattern match on. So we have to store this
          extra information somewhere along with the list of blocks. Now we have information
          doubling, which is not very pretty.
          This could be avoided if the blocks were a syntactic construct, so that you could
          pattern match on them and read out the `assume`s.
        - We'd have to decide the propositions. Often this will be easy, since those propositions
          often stem from `if` and the like. However, Boogie allows arbitrary propositions in
          `assume`, which may even include forall-quantifiers.
          This means we have to read some variables with `Mem.get`, which we know doesn't change
          the state after interpretation, but theoretically we can't know this at this point;
          it also breaks eutt.
      2. We can use an "event oracle", i.e. add an effect to our ITrees so that we can ask
        the world which branch to take. This is (oversimplifying) how
        (Choice Trees)[https://arxiv.org/pdf/2211.06863] paper does it, but there are subtleties
        to consider, such as:
        - For `ITree MemEv A`, we have some nice laws such as associativity after interpretation.
          But you don't want to interpret `ITree (MemEv ⊕ NonDet) A`, because... you can't.
          So what do you do? You need to recover this structure somehow, and that's what the
          CTrees paper is for. See section 2.2 of the ctrees paper.
        - A different notion of program equivalence than eutt, which can deal with non-det.
      3. So instead, we take a very practical, somewhat hacky, approach for now: For each
        destination block, jump to the first block whose `assume φ` decides to true.
        This will coincidentally give us correct semantics if the assumes are disjoint, and will
        act as a tie-breaker for non-determinism.
        - The problem with having to *look inside* the blocks and read out the `assume`s remain.
    -/




-- ## Example:

def bb1 : Block := {
  code := do
    Mem.write "i1" 1
    return ⟨[2], by rw [List.length]; omega⟩
}

def bb2 : Block := {
  assumes := do return (<- Mem.read "i") <= 5
  code := do
    Mem.write "x" ((<- Mem.read "x") + 2)
    Mem.write "i" ((<- Mem.read "i") + 1)
    return ⟨[2, 3], by rw [List.length]; omega⟩
}

def bb3 : Block := {
  assumes := do return !((<- Mem.read "i") <= 5)
  code := do return ⟨[0], by rw [List.length]; omega⟩
}

def myProc : Procedure := {
  blocks := [bb1, bb2, bb3]
}

-- theorem run_step : Procedure.run proc l = proc.blocks[l] >>> proc.run l := sorry

-- example : myProc.run ~~~ myProc.run := by

--   done

-- #check ITree.iter
-- /-- -/
-- example : KTree MemEv Nat Nat :=
--   KTree.iter
