import Std
import Aesop

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

example : StW.pure 123                             = (fun post s => post (123, s)) := rfl
example : StW.pure 123 (fun (_, s) => s < 200)     = (fun s => s < 200)            := rfl
example : StW.pure 123 (fun (n, _) => n = 123) 200                                 := rfl

-- ## Monad Morphism from M to W / Effect observation

def θ (m : St A) : StW A := fun (post : A × S -> Prop) (s₀ : S) => post (m s₀)
def StW.le (w1 w2 : StW A) : Prop := ∀p s, w2 p s -> w1 p s -- [DM4All 3.1]
instance : LE (StW A) := ⟨StW.le⟩
-- Important for θ to be a monad morphism [DM4All 3.1]
theorem θ_bind {a : St A} {b : A -> St B} : θ (a >>= b) = (θ a >>= fun a => θ (b a)) := rfl


-- ## (Verification Helper)
-- Basically the Dijkstra monad, but instead of `.. -> @Subtype M W`, it is `.. -> W -> M -> Prop`

def StV {A : Type} (w : StW A) (m : St A) : Prop := θ m <= w

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

def Equivalent (m₁ m₂ : St A) := θ m₁ <= θ m₂  ∧  θ m₂ <= θ m₂


/-- ## Dijkstra Monad
  Intuitively: The set of all computations which live up to the specification.
  This is useful if you want to write code that is verified from the get-go, and then you can
  write e.g. division where division by zero never occurs.

  But that is not what we want for equivalanence checking: When equivalence checking, we already
  have a program `m : St A`, and we want to show that it lives up to a spec.
-/
def StD (A : Type) (w : StW A) : Type := {m : St A // θ m <= w} -- `θ m <= w` = `StV w m`
def StD.pure (a : A) : StD A (StW.pure a) := ⟨St.pure a, StV.pure a⟩
def StD.bind {wa : StW A} {wb : A -> StW B} (da : StD A wa) (db : (a:A) -> StD B (wb a)) : StD B (StW.bind wa wb) := ⟨ St.bind da.1 (fun a => (db a).1), StV.bind da.2 (fun a => (db a).2)⟩
def StD.weaken {w1 w2 : StW A} (weaker : w1 <= w2) : StD A w1 -> StD A w2 := sorry

section Example
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

  /-- Let's show that p1 increments the state by less than 10.
    Note that `StV w : St _ -> Prop` is a predicate which describes the set of valid computations. -/
  example : StV (fun post s => ∀s' < s + 10, post ((), s')) p1 := by
    simp [StV, θ.eq_unfold, LE.le, StW.le]
    intro post s h_post
    rw [p1]
    simp only [St.read.eq_unfold, St.write.eq_unfold, St.bind_push_state]
    have := h_post (s+2) (by unfold S; omega)
    exact this
end Example
