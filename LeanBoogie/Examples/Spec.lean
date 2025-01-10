import LeanBoogie.Effect.AmAtCh

open ITree LeanBoogie

def unsign (x : Int) : ITree Choice Int := do
  if <- choice Bool then
    return x
  else
    return -x

def unsignW (x : Int) : ITree0W Int := ⟨
  fun Post => Post (return x) ∧ Post (return -x),
  by aesop
⟩

theorem unsignW₂ : θ (return -x : ITree0 Int) <= (unsignW x) := by
  dsimp [unsignW, θ]
  intro Post h
  simp at h
  dsimp [Pure.pure, θ]
  exact h.2

def foo : ITree (AmAt & Choice) Int := do
  let c <- choice (Fin 3)
  assume (c > 1)
  return c * 2

def foo' : ITree (AmAt & Choice) Int :=
  ITree.vis (.right <| Choice.ch (Fin 3)) fun c =>
    ITree.vis (.left <| AmAt.am (c >= 1)) fun ⟨_prf⟩ =>
      return (c * 2)

def fooW : ITree0W Int := ⟨
  fun (Post : ITree0 Int -> Prop) =>
    ∀c : Fin 3, -- `Choice.ch (Fin 3)`
      c >= 1 -> -- `AmAt.am (c >= 1)`
        Post (return c * 2), -- `return c * 2`
  by aesop⟩

example : θ foo' = sorry := by
  rw [foo']
  rw [AmAtCh.θ_ch]
  simp only [AmAtCh.θ_am]
  simp [LawfulTheta.θ_pure]
  sorry

theorem foo_fooW : θ foo' <= fooW := by sorry

theorem fooW_2 : θ (return 2 : ITree0 Int) <= fooW := by
  dsimp [fooW, θ]
  intro Post h
  simp at h
  dsimp [Pure.pure, θ, ITree0.θ]
  exact h 1 (by aesop)

theorem fooW_4 : θ (return 4 : ITree0 Int) <= fooW := by
  dsimp [fooW, θ]
  intro Post h
  simp at h
  dsimp [Pure.pure, θ, ITree0.θ]
  exact h 2 (by aesop)

def divW : ITree0W Int := ⟨
  fun Post => Post spin ,
  sorry
⟩
