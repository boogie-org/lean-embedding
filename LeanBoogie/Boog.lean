import Std
open Std (HashSet HashMap)

namespace Boog

-- Lean-auto is able to reason about strings just fine:
-- example : "a" ++ "b" = "ab" := by auto

-- # Boogie state monad

-- structure BoogieState where
  -- vars : Std.HashMap String Int
abbrev BoogieState := String -> Int
-- deriving Inhabited

abbrev Boog : Type -> Type := StateM BoogieState

def Boog.skip : Boog Unit := pure ()
def Boog.seq (a b : Boog Unit) : Boog Unit := do a; b

-- def update [DecidableEq A] (f : A -> B) (a : A) (b : B) : A -> B :=
--   fun x => if x = a then b else f x
def update (a : String) (b : Int) : (String -> Int) -> (String -> Int) :=
  fun f x => if x = a then b else f x

def Boog.set (v : String) (e : Boog Int) : Boog Unit := do
  let val <- e
  -- modifyThe BoogieState (fun s => { s with vars := s.vars.insert v val })
  modifyThe BoogieState
      (fun f x => if x = v then val else f x)
    -- (update v val)

def Boog.get (v : String) : Boog Int := do
  let state <- getThe BoogieState
  return state v
  -- return (<- getThe BoogieState).vars.getD v 0

def Boog.ifthen (c : Boog Bool) (t : Boog Unit) : Boog Unit := do
  if <- c then t

def Boog.ifthenelse (c : Boog Bool) (t e : Boog Unit) : Boog Unit := do
  if <- c then t else e

-- # Using HashMap instead...

-- Lean-auto doesn't deal well with this:
-- example (m : Std.HashMap String Int) :
--     (m.insert "a" 1).insert "a" 0
--   = (m.insert "a" 2).insert "a" 0
--   := by auto
--
-- But we can provide lemmas like these:
-- theorem HashMap.lww (m : Std.HashMap String B) : (m.insert a val1).insert a val2 = m.insert a val2 := by
--   sorry
