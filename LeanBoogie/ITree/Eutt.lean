import LeanBoogie.ITree.ITree

inductive EuttF (R : ITree E A → ITree E A → Prop) : ITree E A → ITree E A → Prop
| ret : EuttF R (.ret r) (.ret r)
| vis : (∀ a, R (k₁ a) (k₂ a)) → EuttF R (.vis e k₁) (.vis e k₂)
| tau  : R x y → EuttF R (.tau x) (.tau y)
| taul : R x y → EuttF R (.tau x) y
| taur : R x y → EuttF R x (.tau y)

/-- Equivalence-up-to-tau, i.e., weak bisimiulation. This is called `eutt` in the Coq development -/
inductive Eutt (x y : ITree E A) : Prop where
| intro
  (R : ITree E A → ITree E A → Prop)
  (h_fixpoint : ∀a b, R a b → EuttF R a b)
  (h_R : R x y)

theorem Eutt.refl (x : ITree E A) : Eutt x x := by
  apply Eutt.intro (R := (· = ·))
  · rintro a b rfl
    cases a
    · constructor
    · constructor; rfl
    · constructor; intro; rfl
  · rfl

theorem Eutt.symm {x y : ITree E A} : Eutt x y → Eutt y x := by
  rintro ⟨R, isFixpoint, h_R⟩
  apply Eutt.intro (R := flip R)
  · intro a b h_fR
    cases isFixpoint b a h_fR
    <;> constructor
    <;> assumption
  · exact h_R

theorem Eutt.trans {x y z : ITree E A} : Eutt x y → Eutt y z → Eutt x z := by
  rintro ⟨R₁, isFixpoint₁, h_R₁⟩ ⟨R₂, isFixpoint₂, h_R₂⟩
  let R' (a c) := ∃ b, R₁ a b ∧ R₂ b c
  apply Eutt.intro (R := R')
  · rintro a c ⟨b, h_fR₁, h_fR₂⟩
    specialize isFixpoint₁ _ _ h_fR₁
    specialize isFixpoint₂ _ _ h_fR₂
    clear h_fR₁ h_fR₂

    cases isFixpoint₁
    case ret r =>
      generalize r = retr
      -- split at isFixpoint₂
      -- cases isFixpoint₂
      sorry
    case vis e k => sorry
    case tau t => sorry
    case taul t => sorry
    case taur t => sorry
  · exact ⟨y, h_R₁, h_R₂⟩

instance ITree.setoid : Setoid (ITree E A) where
  r := Eutt
  iseqv := ⟨Eutt.refl, Eutt.symm, Eutt.trans⟩

instance Internal.ITree.setoid : Setoid (ITree E A) := _root_.ITree.setoid -- typeclass resolution isn't able to figure this out on its own...

theorem Eutt.ret : @ITree.ret E A r ≈ .ret r := Eutt.refl _

theorem Eutt.ret_congr {a b : A} (h : a = b) : @ITree.ret E A a ≈ .ret b := h ▸ Eutt.refl _

inductive Rel : ITree E A -> ITree E A -> Prop
| refl : Rel t t
| taur : Rel t (.tau t)

theorem Eutt.taur {t : ITree E A} : t ≈ t.tau := by
  let R (x y : ITree E A) : Prop := Rel x y
  have hFix (a b : ITree E A) (h : R a b) : EuttF R a b := by
    cases a
    case ret r =>
      cases h
      case refl => exact EuttF.ret
      case taur => exact EuttF.taur .refl
    case tau t =>
      cases h
      case refl => exact EuttF.tau .refl
      case taur => exact EuttF.tau .taur
    case vis e k =>
      sorry
      -- cases h
      -- case refl => done
      -- case tau => done
  have hR : R t (.tau t) := .taur
  exact .intro R hFix hR

theorem Eutt.taul {t : ITree E A} : t.tau ≈ t := sorry
theorem Eutt.tau  {t : ITree E A} : t.tau ≈ t.tau := sorry
theorem Eutt.tau_congr  {t : ITree E A} : t ≈ u -> t.tau ≈ u.tau := sorry

-- See page 8 of the ITree paper
-- theorem bind_congr : Eutt t1 t2 -> EuttK k1 k2 -> Eutt (ITree.bind t1 k1) (ITree.bind t2 k2) := trustITree "page 8"
-- theorem vis_congr : EuttK k1 k2 -> Eutt (.vis e k1) (.vis e k2) := trustITree "page 8"
-- theorem tau_congr : Eutt t1 t2 -> Eutt (.tau t1) (.tau t2) := trustITree "page 8"

theorem Eutt.vis {k₁ k₂ : Ans → ITree E A} : k₁ ≈ k₂ -> ITree.vis e k₁ ≈ .vis e k₂ := by
  sorry
