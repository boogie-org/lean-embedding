import LeanBoogie.ITree
import LeanBoogie.Util
import LeanBoogie.Boogie

#check 1
open LeanBoogie

-- # Coinduction, Interaction Trees

inductive Delay' (A : Type) : Type
| ret : A        -> Delay' A
| tau : Delay' A -> Delay' A
-- _Problem_: This is always finite
-- def spin' : Delay' A := Delay'.tau spin' -- fails

codata Delay A where
| ret : A       -> Delay A
| tau : Delay A -> Delay A

def spin : Delay A := MvQPF.Cofix.corec (fun s => .tau s) 0 -- :)

codata ITree_ E A where
| ret : A          -> ITree_ E A
| tau : ITree_ E A -> ITree_ E A
| vis : E → (Int → ITree_ E A) → ITree_ E A
--            ^^^ hard-coded answer type for now, due to limitation with QPFTypes

/-- _Equivalence up to tau_. Notation: `~~` -/
inductive Eutt_ : ITree E A → ITree E A → Prop
| ret : Eutt_ (.ret r) (.ret r)
| vis : (∀ a, Eutt (k₁ a) (k₂ a)) → Eutt_ (.vis e k₁) (.vis e k₂)
| tau  : Eutt x y → Eutt_ (.tau x) (.tau y)
| taul : Eutt x y → Eutt_ (.tau x) y
| taur : Eutt x y → Eutt_ x (.tau y)

/-
  # ITrees form an (iterative) monad
  These are our three central primitives
-/
def pure (a : A) : ITree E A                                                                        := ITree.ret a
def bind (ta : ITree E A) (tb : A -> ITree E B) : ITree E B                                         := ITree.bind ta tb
def iter (body : A -> ITree E (A ⊕ B)) (a₀ : A) : ITree E B                                         := sorry

theorem iter_fp {f : A -> ITree E (A ⊕ B)} {a : A}
  :  iter f a
  = f a >>= (fun
               | .inl a => iter f a -- continue
               | .inr b => return b -- stop iterating
             )
  := ITree.trustITree "ITree paper page 9"

/- # Memory

  `ITree MemEv A`      ---(interp)--->      `S -> ITree Empty (A × S)`
-/

inductive MemEv /- Type -> -/ : Type where
| read  : String        -> MemEv /- Int -/
| write : String -> Int -> MemEv /- Unit -/

def Mem.read  (v : String)             : ITree MemEv Int  := .vis (.read v)      (fun (ans : Int) => .ret ans)
def Mem.write (v : String) (val : Int) : ITree MemEv Unit := .vis (.write v val) (fun (_unit : _) => .ret ())

def BoogieState_ : Type := String -> Int
-- def St_           (A : Type) : Type := BoogieState ->         (A × BoogieState)
def Boogie_ (E : Type) (A : Type) : Type := BoogieState -> ITree E (A × BoogieState)

def interp (tm : ITree MemEv A) : Boogie A := fun s₀ =>
  ITree.corec (fun ⟨tm, s⟩ =>
    match tm.dest with
    | .ret a => .ret (a, s)
    | .tau t => .tau (t, s)
    | .vis (.read v) k => .tau ⟨k (s v), s⟩
    | .vis (.write v val) k => .tau ⟨k (default), s.update v val⟩
  ) (tm, s₀)

theorem interp_pure : interp (ITree.pure x) = Boogie.pure x := sorry!
--                                            ^^^^^^^^^^^ : `BoogieState -> ITree Empty (A × BoogieState)`
--                            ^^^^^^^^^^^^ : `ITree MemEv A`

theorem interp_bind {ta : ITree MemEv A} {tb : A -> ITree MemEv B}
  : interp (ITree.bind ta tb)       =      Boogie.bind (interp ta) (fun a => interp (tb a))
  := sorry!

theorem interp_iter {body : A -> ITree MemEv (A ⊕ B)} {a₀ : A}
  : interp (ITree.iter body a₀)    =       Boogie.iter (fun (a : A) => interp (body a)) a₀
  := sorry!
