import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.AlgebraicTopology.SingularSet
import TopCatModelCategory.MorphismProperty
import TopCatModelCategory.Factorization
import TopCatModelCategory.SSet.Skeleton
--import TopCatModelCategory.ModelCategoryTopCat
import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.SSet.Presentable
import TopCatModelCategory.JoyalTrickDual
import Mathlib.CategoryTheory.SmallObject.Basic

open HomotopicalAlgebra CategoryTheory Limits

namespace SSet

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace modelCategoryQuillen

open MorphismProperty SmallObject

instance (K : Type u) [LinearOrder K] : HasIterationOfShape K SSet.{u} where

attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

instance (J : Type u) [SmallCategory J] [IsFiltered J] (X : SSet.{u}) [X.IsFinite] :
    PreservesColimitsOfShape J (coyoneda.obj (Opposite.op X)) := by
  have : IsCardinalFiltered J Cardinal.aleph0.{u} := by
    rwa [isCardinalFiltered_aleph0_iff]
  exact preservesColimitsOfShape_of_isCardinalPresentable _ (Cardinal.aleph0.{u}) _

instance isCardinalForSmallObjectArgument_I :
    I.{u}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} where
  hasIterationOfShape := by infer_instance
  preservesColimit i hi f hf := by
    obtain ⟨n⟩ := hi
    infer_instance
  isSmall := by
    dsimp [I]
    infer_instance

instance isCardinalForSmallObjectArgument_J :
    J.{u}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} where
  hasIterationOfShape := by infer_instance
  preservesColimit i hi f hf := by
    simp only [J, iSup_iff] at hi
    obtain ⟨n, ⟨i⟩⟩ := hi
    infer_instance
  isSmall := by
    dsimp [J]
    infer_instance

instance : HasSmallObjectArgument.{u} I.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

instance : HasSmallObjectArgument.{u} J.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

instance : CategoryWithWeakEquivalences TopCat.{0} := sorry
instance : (weakEquivalences TopCat).HasTwoOutOfThreeProperty := sorry
instance : (weakEquivalences TopCat).IsStableUnderRetracts := sorry

instance : CategoryWithWeakEquivalences SSet.{0} where
  weakEquivalences :=
    (weakEquivalences TopCat).inverseImage SSet.toTop

lemma weakEquivalences_eq :
    weakEquivalences SSet.{0} =
      (weakEquivalences TopCat).inverseImage SSet.toTop := rfl

lemma weakEquivalence_iff {X Y : SSet.{0}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (toTop.map f) := by
  simp only [HomotopicalAlgebra.weakEquivalence_iff]
  rfl

instance : (weakEquivalences SSet).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_eq]
  infer_instance

instance : (weakEquivalences SSet).IsStableUnderRetracts := by
  rw [weakEquivalences_eq]
  infer_instance

instance : (cofibrations SSet).IsStableUnderRetracts := by
  rw [cofibrations_eq]
  infer_instance

instance : (fibrations SSet).IsStableUnderRetracts := by
  rw [fibrations_eq]
  infer_instance

lemma rlp_I_le_rlp_J : I.{u}.rlp ≤ J.{u}.rlp := by
  rw [← le_llp_iff_le_rlp, llp_rlp_of_isCardinalForSmallObjectArgument _ .aleph0,
    transfiniteCompositions_pushouts_coproducts]
  exact J_le_monomorphisms.trans (le_retracts _)

instance : HasFunctorialFactorization (trivialCofibrations SSet) (fibrations SSet) := by
  refine MorphismProperty.hasFunctorialFactorization_of_le (W₁ := J.rlp.llp)
    (W₂ := J.rlp) ?_ (by rfl)
  rw [trivialCofibrations, le_inf_iff,
    llp_rlp_of_isCardinalForSmallObjectArgument _ .aleph0]
  constructor
  · simpa [cofibrations_eq] using J_le_monomorphisms
  · sorry -- J is mapped by the realization functor to trivial cofibrations in `TopCat`

-- the topological realization of a fibration of simplicial sets is a Serre fibration
--instance {X Y : SSet.{0}} (f : X ⟶ Y) [Fibration f] :
--    Fibration (toTop.map f) :=
--  sorry

lemma weakEquivalence_iff_of_fibration {X Y : SSet.{0}} (f : X ⟶ Y) [Fibration f] :
    I.rlp f ↔ WeakEquivalence f :=
  sorry

lemma rlp_I_eq_trivialFibrations :
    I.rlp = trivialFibrations SSet := by
  ext X Y f
  rw [mem_trivialFibrations_iff]
  constructor
  · intro hf
    obtain : Fibration f := by simpa only [fibration_iff] using rlp_I_le_rlp_J _ hf
    exact ⟨inferInstance, by rwa [← weakEquivalence_iff_of_fibration]⟩
  · rintro ⟨_, _⟩
    rwa [weakEquivalence_iff_of_fibration]

instance : HasFunctorialFactorization (cofibrations SSet) (trivialFibrations SSet) := by
  refine MorphismProperty.hasFunctorialFactorization_of_le (W₁ := I.rlp.llp) (W₂ := I.rlp) ?_
    (by rw [rlp_I_eq_trivialFibrations])
  rw [llp_rlp_of_isCardinalForSmallObjectArgument _ .aleph0, cofibrations_eq,
    transfiniteCompositions_pushouts_coproducts]
  apply retracts_le

instance {A B X Y : SSet.{0}} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [hp : WeakEquivalence p] :
    HasLiftingProperty i p := by
  have : I.rlp p := by
    rw [rlp_I_eq_trivialFibrations]
    exact mem_trivialFibrations p
  rw [I_rlp_eq_monomorphisms_rlp] at this
  exact this _ (mono_of_cofibration _)

end modelCategoryQuillen

open modelCategoryQuillen

instance : ModelCategory SSet.{0} where
  cm4a i p _ _ _ := ModelCategory.joyal_trick_dual
    (by intros; infer_instance) _ _

end SSet
