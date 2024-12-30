import Mathlib.AlgebraicTopology.ModelCategory.JoyalTrick

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
    HasLiftingProperty i p := by
  sorry

end HomotopicalAlgebra.ModelCategory
