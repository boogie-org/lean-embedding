import Std
import Aesop
import Auto
import Duper

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.printLemmas true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"
set_option pp.fieldNotation.generalized false

-- # Dijkstra Monad for non-ITree StateT

-- ## Computation Monad

abbrev S := Int
abbrev St (A: Type) : Type := S -> (A × S)
def St.pure {A : Type} (a : A) : St A := fun s => (a, s)
def St.bind {A : Type} (a : St A) (b : A -> St B) : St B := fun s => let res := a s;   b res.1 res.2
-- ? St.iter
instance : Monad St := { pure := St.pure, bind := St.bind }
theorem St.bind_push_state {a : St A} {b : A -> St B} : (a >>= b) σ = (b (a σ).fst (a σ).snd) := rfl
def St.read : St Int := fun s => (s, s)
def St.write (a : Int) : St Unit := fun _ => ((), a)

/- ## Specification Monad
  In this case, computing the weakest preconditions.
-/

abbrev StW (A : Type) : Type := (A × S -> Prop) -> S -> Prop
def StW.pure {A : Type} (a : A) : StW A :=
  fun (p : A × S → Prop) (s : S) => p (a, s)
def StW.bind {A : Type} (wa : StW A) (wb : A -> StW B) : StW B :=
  fun (pb : B × S → Prop) (s₀ : S) => wa (fun res => wb res.1 pb res.2) s₀
-- ? StW.iter
instance : Monad StW := { pure := StW.pure, bind := StW.bind }
theorem StW.bind_push_state {a : StW A} {b : A -> StW B} {post : B × S -> Prop} {σ : S} : (a >>= b) post σ = a (fun res => b res.fst post res.snd) σ := rfl
def StW.read : StW Int := fun (post : Int × S → Prop) (s:S) => post (s, s)
def StW.write (a : Int) : StW Unit := fun (post : Unit × S → Prop) (_:S) => post ((), a)
def StW.and (v w : StW A) : StW A := fun post s => (v post s) ∧ (w post s)

example : StW.pure 123                             = (fun post s => post (123, s)) := rfl
example : StW.pure 123 (fun (_, s) => s < 200)     = (fun s => s < 200)            := rfl
example : StW.pure 123 (fun (n, _) => n = 123) 200                                 := rfl

/-- Allows us to create a specification from arbitrary pre-conditions and post-conditions.
  Source: [DM4Ever] page 15. -/
def encode (pre : S -> Prop) (post : (A × S) -> Prop) : StW A :=
  fun p s => pre s ∧ (∀r, post r -> p r)

-- ## Monad Morphism from M to W / Effect observation

def θ (m : St A) : StW A :=
  fun (post : A × S -> Prop) (s₀ : S) =>
    post (m s₀)

def StW.le (w1 w2 : StW A) : Prop := ∀p s, w2 p s -> w1 p s -- [DM4All 3.1]
instance : LE (StW A) := ⟨StW.le⟩

-- Important for θ to be a monad morphism [DM4All 3.1]
theorem θ_pure : θ (return a) = return a := rfl
theorem θ_bind : θ (a >>= b) = (θ a >>= fun a => θ (b a)) := rfl

def θ_if [Decidable φ] {t e : St A}
  : θ (if φ then t else e)
  = if φ then θ t else θ e
  := by
  split
  next h => simp_all only
  next h => simp_all only

def θ_if' [Decidable φ] {t e : St A}
  : θ (if φ then t else e)
  = (fun post s => (φ -> θ t post s) ∧ (¬φ -> θ e post s))
  := by
  split
  next h => simp_all only [true_implies, not_true_eq_false, false_implies, and_true]
  next h => simp_all only [false_implies, not_false_eq_true, true_implies, true_and]

def θ_read : θ (St.read) = StW.read := rfl
def θ_write : θ (St.write val) = StW.write val := rfl

theorem verify_ite [Decidable φ] {w t e : StW A}
  (tru :  φ -> t <= w)
  (fal : ¬φ -> e <= w)
  : (if φ then t else e) <= w
  := by aesop

-- ## (Verification Helper)
-- Basically the Dijkstra monad, but instead of `.. -> @Subtype M W`, it is `.. -> W -> M -> Prop`

def StV {A : Type} (w : StW A) (m : St A) : Prop := θ m <= w
instance : Membership (St A) (StW A) := ⟨StV⟩
def Equivalent (m₁ m₂ : St A) := θ m₁ <= θ m₂  ∧  θ m₂ <= θ m₁

/-- There exists exactly one program which returns `a`. -/
theorem StV.pure  (a : A) : StV (StW.pure a) (St.pure a) := by
  dsimp [StV, LE.le, StW.le, θ]
  intro p s h
  exact h

/- If we have `ma >>= mb`, then in order to prove `StV (wa >>= wb)` about  `ma >>= mb`, it is
  sufficient to prove `StV wa ma` and `∀a, StV (wb a) (mb a)`.

  ...However, imagine the following situation: Let `w : StW B` is a spec which says that the state
  gets incremented by `2`. Let `m : St B` be `m :≡ (increment by 1) >>= (increment by 1)`.
  Now, `m` is composed of a `St.bind`, but `w` is not. Using `StV.bind` to prove that `m` adheres
  to `w` is not the best way.
  So while this rule is handy for proving that a program lives up to a structurally similar spec,
  it is not the most general way of proving that an arbitrary program lives up to an arbitrary spec.
-/
theorem StV.bind
  {ma :      St A} {wa :      StW A} (a :            StV wa     ma    )
  {mb : A -> St B} {wb : A -> StW B} (b : (a : A) -> StV (wb a) (mb a))
  : StV (StW.bind wa wb) (St.bind ma mb)
  := by
    dsimp only [StV, θ.eq_unfold, LE.le, StW.le, St.bind, StW.bind]
    dsimp only [StV, θ.eq_unfold, LE.le, StW.le] at a b
    intro post s h
    have := b (ma s).1 post (ma s).2
    have := a (fun mas => wb mas.1 post mas.2) s
    simp_all only [imp_self, true_implies]

theorem StV.weaken (weaker : w₁ <= w₂) (mv : StV w₁ m) : StV w₂ m := by
  dsimp only [StV, θ.eq_unfold, LE.le, StW.le] at *
  intro post s h
  simp_all only

theorem if_fun_push [Decidable φ] {α β : X -> Y}
  : (if φ then fun x => α x else fun x => β x) x
  = (if φ then α x else β x) := by aesop

theorem if_Prop [Decidable φ] : (if φ then α else β) = ((φ -> α) ∧ (¬φ -> β)) := by aesop

/-- ## Dijkstra Monad
  Intuitively: The set of all computations which live up to the specification.
  This is useful if you want to write code that is verified from the get-go, and then you can
  write e.g. division where division by zero never occurs.

  But that is not what we want for equivalanence checking: When equivalence checking, we already
  have a program `m : St A`, and we want to show that it lives up to a spec.
-/
def StD (A : Type) (w : StW A) : Type := {m : St A // θ m <= w}
def StD.pure (a : A) : StD A (StW.pure a) := ⟨St.pure a, StV.pure a⟩
def StD.bind {wa : StW A} {wb : A -> StW B} (da : StD A wa) (db : (a:A) -> StD B (wb a)) : StD B (StW.bind wa wb) := ⟨ St.bind da.1 (fun a => (db a).1), StV.bind da.2 (fun a => (db a).2)⟩
def StD.weaken {w1 w2 : StW A} (weaker : w1 <= w2) : StD A w1 -> StD A w2 := fun ⟨m, w⟩ => ⟨m, StV.weaken weaker w⟩

namespace Example1
  def p1 : St Unit := do
    let x <- St.read
    St.write (x+2)

  def p2 : St Unit := do
    let x <- St.read
    St.write (x+1)
    let x <- St.read
    St.write (x+1)

  /-- Let's show that p1 increments the state by 2. -/
  example : StV (fun post s => post ((), s+2)) p1 := by
    simp [StV, θ.eq_unfold, LE.le, StW.le]
    intro post s h -- h intuitively is "if it holds for the spec..."
    -- ⊢ "...then it also holds for p1"
    -- So now, if you can show that `p1 s = s+2` then you've won.
    rw [p1]
    simp only [St.read.eq_unfold, St.write.eq_unfold, St.bind_push_state]
    exact h

  example : StV (encode (. = 0) (. = ((), 2))) p1 := by
    simp [StV, θ.eq_unfold, LE.le, StW.le, encode]
    intro post h
    rw [p1]
    simp only [St.read.eq_unfold, St.write.eq_unfold, St.bind_push_state]
    exact h

  /-- Let's show that p1 increments the state by less than 10.
    Note that `StV w : St _ -> Prop` is a predicate which describes the set of valid computations. -/
  example : StV (fun post s => ∀s' < s + 10, post ((), s')) p1 := by
    simp [StV, θ.eq_unfold, LE.le, StW.le]
    intro post s h_post
    rw [p1]
    simp only [St.read.eq_unfold, St.write.eq_unfold, St.bind_push_state]
    have := h_post (s+2) (by unfold S; omega)
    exact this

  /-- `θ p1 (fun ((), s') => s' < s + 10) : BoogieState -> Prop` describes the set of initial states
    for which, after executing p1, the postcondition holds. -/
  example (s) : θ p1 (fun ((), s') => s' < s + 10) s := by
    rw [p1]
    rw [θ_bind]
    rw [θ.eq_unfold]
    simp only
    rw [St.read.eq_unfold, St.write.eq_unfold]
    simp only [bind, StW.bind]
    unfold S; omega
end Example1

namespace Example2
  def abs : St Int := do
    if (<- St.read) < 0
      then return - (<- St.read)
      else return (<- St.read)

  def abs' : St Int := do
    let x <- St.read
    if x >= 0 then return x else return -x

  example : θ abs <= θ abs' := by
    intro rhs_post s rhs_post_h
    simp [abs, abs'] at *
    simp [θ_pure, θ_bind, θ_read, θ_write, θ_if] at *
    simp [StW.read.eq_unfold, StW.pure.eq_unfold, Pure.pure, Bind.bind, StW.bind.eq_unfold, StW.pure.eq_unfold] at *
    simp [if_fun_push] at *
    rw [if_Prop] at *
    -- rhs_post_h : (0 ≤ s → rhs_post (s, s)) ∧ (¬0 ≤ s → rhs_post (-s, s))
    -- ⊢ (s < 0 → rhs_post (-s, s)) ∧ (¬s < 0 → rhs_post (s, s))
    obtain ⟨left, right⟩ := rhs_post_h
    constructor
    . sorry
    . sorry
end Example2

namespace Example3
  def f (x : Int) : St Unit := do
    let a <- St.read
    St.write (a + x)
    let a <- St.read
    St.write (a + x)

  def g (x : Int) : St Unit := do
    let a <- St.read
    St.write (a + (2 * x))

  theorem bad_approach : θ (f x) <= θ (g x) := by
    intro rhs_post s rhs_post_h
    rw [θ] at * -- bad: we don't want to unfold θ so soon! Only at the leaves.
    -- Now we have `rhs_post (g x s) ⊢ rhs_post (f x s)` which defeats the purpose of `θ`.
    simp [f, g] at *
    -- Now we have `rhs_post_h : rhs_post ((St.read >>= fun tmp => St.write (tmp + 2 * x)) s)`,
    -- which is not as handy as the better approach
    sorry

  /- Taking a step back, recall that `θ` is a monad morphism, so it is compatible with `pure`, `bind`.
    We can thus push θ inwards. -/
  theorem good_approach : θ (f x) <= θ (g x) := by
    simp [f, g] at *
    simp [θ_pure, θ_bind, θ_read, θ_write, θ_if] at *
    simp [StW.write.eq_unfold, StW.read.eq_unfold] at *
    dsimp [Pure.pure, Bind.bind]
    rw [StW.bind.eq_unfold]
    simp [Pure.pure, Bind.bind, StW.bind.eq_unfold, StW.pure.eq_unfold] at *
    intro post s rhs_post_h
    -- revert post s rhs_post_h
    have : x + x = 2 * x := by omega
    simp only [this, Int.add_assoc, rhs_post_h]

  def fW (x : Int) : StW Unit :=
    fun (Post : _ -> Prop) =>
      fun s => Post ((), s + 2 * x)

  example (wa : StW A) (wb : A -> StW B) (post) : StW.bind wa wb post = sorry := by
    rw [StW.bind.eq_unfold]
    simp
    sorry

  example : θ (f x) <= fW x := by
    unfold f fW
    intro post s h
    simp [θ_pure, θ_bind, θ_read, θ_write, θ_if] at *
    simp [StW.write.eq_unfold, StW.read.eq_unfold] at *
    dsimp [Pure.pure, Bind.bind]
    rw [StW.bind.eq_unfold]
    simp [Pure.pure, Bind.bind, StW.bind.eq_unfold, StW.pure.eq_unfold] at *
    sorry

  /-- Given postcondition, compute wp. -/
  example : fW 10 (fun ⟨(), s'⟩ => s' < 0) = (fun s => s < -20) := by
    unfold fW
    simp
    ext s
    unfold S at *
    omega
end Example3
