import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.JoyalTrick
import Mathlib.CategoryTheory.MorphismProperty.Limits

open CategoryTheory Category Limits

namespace HomotopicalAlgebra.ModelCategory

variable {C : Type*} [Category C]
  [CategoryWithCofibrations C] [CategoryWithFibrations C] [CategoryWithWeakEquivalences C]

lemma joyal_trick_dual [MorphismProperty.HasFactorization (trivialCofibrations C) (fibrations C)]
  [(weakEquivalences C).HasTwoOutOfThreeProperty] [HasPullbacks C]
  [(fibrations C).IsStableUnderComposition] [(fibrations C).IsStableUnderBaseChange]
  (h : ∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [WeakEquivalence p] [Fibration p],
      HasLiftingProperty i p) {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence i] :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := by
    have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
      (pullback.lift f i sq.w)
    have sq' : CommSq h.i i (h.p ≫ pullback.snd _ _) (𝟙 B) := ⟨by simp⟩
    have h₁ : WeakEquivalence (h.i ≫ h.p ≫ pullback.snd p g) := by simpa
    have h₂ := MorphismProperty.comp_mem _ _ _
       h.hp ((fibrations C).of_isPullback (IsPullback.of_hasPullback p g) (mem_fibrations p))
    rw [← fibration_iff] at h₂
    have : WeakEquivalence (h.p ≫ pullback.snd p g) := by
      rw [weakEquivalence_iff] at h₁ ⊢
      exact MorphismProperty.of_precomp _ _ _  h.hi.2 h₁
    exact ⟨⟨{ l := sq'.lift ≫ h.p ≫ pullback.fst p g
              fac_right := by
                rw [assoc, assoc, pullback.condition, reassoc_of% sq'.fac_right] }⟩⟩

end HomotopicalAlgebra.ModelCategory
