import LeanBoogie.ITree
import LeanBoogie.Mem
import LeanBoogie.State
import Aesop

open LeanBoogie ITree

def Γ : Con := [.int, .int]
def i : Var Γ .int := .vz
def x : Var Γ .int := .vs .vz

def prog : ITree (Mem Γ) Unit := do
  while_ (Mem.read i >>= (fun i => return i < 3)) do
    Mem.update i (. + 1)
    Mem.update x (. + 2)

def runProg (fuel : Nat) : IO Int := StateT.run' (do
    let _ <- run prog fuel handle
    State.read x
  )
  default

-- feel free to uncomment the rest
#eval timeit "" (runProg 3) -- 12ms, x=0
-- #eval timeit "" (runProg 4) -- 22ms, x=0
-- #eval timeit "" (runProg 5) -- 50ms, x=2
-- #eval timeit "" (runProg 10) -- 1.4s, x=2
-- #eval timeit "" (runProg 15) -- 2.6s, x=4
-- #eval timeit "" (runProg 20) -- 5.5s, x=6
