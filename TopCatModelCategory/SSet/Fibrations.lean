import TopCatModelCategory.SSet.AnodyneExtensions
import TopCatModelCategory.SSet.Monoidal

universe u

open CategoryTheory MonoidalCategory HomotopicalAlgebra Limits

namespace CategoryTheory

namespace MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C]
  {A B X Y : C} [Closed A] [Closed B]

@[reassoc]
lemma curry_whiskerRight_comp (f : A ⟶ B) (g : B ⊗ X ⟶ Y) :
    curry (f ▷ X ≫ g) = curry g ≫ (pre f).app Y := by
  sorry

@[reassoc]
lemma whiskerRight_comp_uncurry (f : A ⟶ B) (g : X ⟶ (ihom B).obj Y) :
    f ▷ X ≫ uncurry g = uncurry (g ≫ (pre f).app Y) := by
  sorry

end MonoidalClosed

end CategoryTheory

namespace SSet

variable {A B X Y : SSet.{u}}

instance (p : X ⟶ Y) [Fibration p] :
    Fibration ((ihom A).map p) := by
  rw [ModelCategory.fibration_iff]
  intro _ _ _ hf
  simp only [ModelCategory.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  rw [← (ihom.adjunction A).hasLiftingProperty_iff]
  apply anodyneExtensions.hasLeftLiftingProperty
  apply anodyneExtensions.whiskerLeft
  exact anodyneExtensions.subcomplexHorn_ι_mem n i

instance {A X : SSet.{u}} [IsFibrant X] : IsFibrant (A ⟶[SSet] X) := by
  rw [isFibrant_iff_of_isTerminal ((ihom A).map (terminal.from X))]
  · infer_instance
  · apply isLimitOfHasTerminalOfPreservesLimit

section

variable {K L : SSet.{u}} (f : K ⟶ L) (i : A ⟶ B) (p : X ⟶ Y)

noncomputable abbrev fromPushoutProduct : pushout (i ▷ K) (A ◁ f) ⟶ B ⊗ L :=
  pushout.desc (B ◁ f) (i ▷ L) (by simp only [whisker_exchange])

noncomputable abbrev ihomToPullback :
    (ihom B).obj X ⟶ pullback ((ihom A).map p) ((MonoidalClosed.pre i).app Y) :=
  pullback.lift ((MonoidalClosed.pre i).app X) ((ihom B).map p) (by simp)

open MonoidalClosed in
noncomputable def arrowMkFromPushoutProductHomEquiv :
    (Arrow.mk (fromPushoutProduct f i) ⟶ Arrow.mk p) ≃
      (Arrow.mk f ⟶ Arrow.mk (ihomToPullback i p)) where
  toFun φ :=
    Arrow.homMk (curry (pushout.inl _ _ ≫ φ.left))
      (pullback.lift (curry (pushout.inr _ _ ≫ φ.left)) (curry φ.right) (by
        have := φ.w
        dsimp at this
        rw [← curry_natural_right, Category.assoc, this, pushout.inr_desc_assoc,
          ← curry_whiskerRight_comp]
        dsimp)) (by
        dsimp
        ext : 1
        · dsimp
          simp only [Category.assoc, pullback.lift_fst,
            ← curry_whiskerRight_comp, ← curry_natural_left,
            pushout.condition_assoc]
        · dsimp
          have := φ.w
          dsimp at this
          simp only [Category.assoc, pullback.lift_snd, ← curry_natural_left,
            ← curry_natural_right, this, pushout.inl_desc_assoc])
  invFun ψ :=
    Arrow.homMk (pushout.desc (uncurry ψ.left) (uncurry (ψ.right ≫ pullback.fst _ _)) (by
        have := ψ.w =≫ pullback.fst _ _
        dsimp at this
        rw [Category.assoc, Category.assoc, pullback.lift_fst] at this
        rw [← uncurry_natural_left, ← this, whiskerRight_comp_uncurry]
        dsimp))
      (uncurry (ψ.right ≫ pullback.snd _ _)) (by
        dsimp only [Arrow.mk_left, Arrow.mk_hom]
        ext : 1
        · have := ψ.w =≫ pullback.snd _ _
          dsimp at this
          rw [Category.assoc, Category.assoc, pullback.lift_snd] at this
          rw [pushout.inl_desc_assoc, pushout.inl_desc_assoc,
            ← uncurry_natural_right, this, uncurry_natural_left]
        · rw [pushout.inr_desc_assoc, pushout.inr_desc_assoc,
            ← uncurry_natural_right, Category.assoc, pullback.condition,
            whiskerRight_comp_uncurry, Category.assoc]
          dsimp)
  left_inv φ := by
    ext : 1
    · dsimp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
        Arrow.homMk_left, Arrow.homMk_right]
      ext : 1
      · rw [pushout.inl_desc, uncurry_curry]
      · rw [pushout.inr_desc, pullback.lift_fst, uncurry_curry]
    · dsimp
      rw [pullback.lift_snd, uncurry_curry]
  right_inv ψ := by
    ext : 1
    · dsimp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
        Arrow.homMk_left, Arrow.homMk_right]
      rw [pushout.inl_desc, curry_uncurry]
    · dsimp only [Arrow.mk_right, Arrow.mk_left, Arrow.mk_hom,
        Arrow.homMk_left, Arrow.homMk_right]
      ext : 1
      · rw [pullback.lift_fst, pushout.inr_desc, curry_uncurry]
      · rw [pullback.lift_snd, curry_uncurry]

lemma hasLiftingProperty_iHomToPullback_iff :
    HasLiftingProperty f (ihomToPullback i p) ↔
      HasLiftingProperty (fromPushoutProduct f i) p := sorry

end

instance {Z : SSet.{u}} (f : A ⟶ B) [Mono f] [IsFibrant Z] :
    Fibration ((MonoidalClosed.pre f).app Z) := by
  sorry

end SSet
