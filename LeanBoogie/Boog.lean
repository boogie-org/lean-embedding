import Std
open Std (HashSet HashMap)

namespace Boog

-- # Boogie state monad

structure BoogieState where
  vars : Std.HashMap String Int
deriving Inhabited

abbrev Boog : Type -> Type := StateM BoogieState

def Boog.skip : Boog Unit := pure ()
def Boog.seq (a b : Boog Unit) : Boog Unit := do a; b

def Boog.set (v : String) (e : Boog Int) : Boog Unit := do
  let val <- e
  modifyThe BoogieState (fun s => { s with vars := s.vars.insert v val })

def Boog.get (v : String) : Boog Int := do
  return (<- getThe BoogieState).vars.getD v 0

def Boog.ifthen (c : Boog Bool) (t : Boog Unit) : Boog Unit := do
  if <- c then t
def Boog.ifthenelse (c : Boog Bool) (t e : Boog Unit) : Boog Unit := do
  if <- c then t else e
