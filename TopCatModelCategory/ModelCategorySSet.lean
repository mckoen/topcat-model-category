import TopCatModelCategory.ModelCategoryTopCat
import TopCatModelCategory.SSet.Subobject

open HomotopicalAlgebra CategoryTheory

namespace SSet

namespace ModelCategory

open MorphismProperty SmallObject

instance (K : Type u) [Preorder K] : HasIterationOfShape SSet.{u} K where

attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

def I : MorphismProperty SSet.{u} := ofHoms (fun n ↦ SSet.boundaryInclusion.{u} n)
def J : MorphismProperty SSet.{u} := ⨆ n, ofHoms (fun i ↦ SSet.hornInclusion.{u} n i)

lemma I_le_monomorphisms : I.{u} ≤ monomorphisms _ := by
  rintro _ _ _ ⟨n⟩
  simp only [monomorphisms.iff]
  infer_instance

lemma J_le_monomorphisms : J.{u} ≤ monomorphisms _ := by
  rintro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  simp only [monomorphisms.iff]
  infer_instance

instance isCardinalForSmallObjectArgument_I :
    I.{u}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} where
  hasIterationOfShape := by infer_instance
  preservesColimit := sorry
  isSmall := by
    dsimp [I]
    infer_instance

instance isCardinalForSmallObjectArgument_J :
    J.{u}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} where
  hasIterationOfShape := by infer_instance
  preservesColimit := sorry
  isSmall := by
    dsimp [J]
    infer_instance

instance : HasSmallObjectArgument.{u} I.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

instance : HasSmallObjectArgument.{u} J.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

instance : CategoryWithCofibrations SSet.{0} where
  cofibrations := monomorphisms _

instance : CategoryWithWeakEquivalences SSet.{0} where
  weakEquivalences :=
    (weakEquivalences TopCat).inverseImage SSet.toTop

instance : CategoryWithFibrations SSet.{0} where
  fibrations := J.rlp

lemma cofibrations_eq : cofibrations SSet.{0} = monomorphisms _ := rfl

lemma fibrations_eq : fibrations SSet.{0} = J.rlp := rfl

lemma weakEquivalences_eq :
    weakEquivalences SSet.{0} =
      (weakEquivalences TopCat).inverseImage SSet.toTop := rfl

section

variable {X Y : SSet.{0}} (f : X ⟶ Y)

lemma cofibration_iff : Cofibration f ↔ Mono f := by
  rw [HomotopicalAlgebra.cofibration_iff]
  rfl

lemma fibration_iff : Fibration f ↔ J.rlp f := by
  rw [HomotopicalAlgebra.fibration_iff]
  rfl

lemma weakEquivalence_iff : WeakEquivalence f ↔ WeakEquivalence (toTop.map f) := by
  simp only [HomotopicalAlgebra.weakEquivalence_iff]
  rfl

end

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

lemma transfiniteCompositions_pushouts_coproducts :
    transfiniteCompositions.{u} I.coproducts.{u}.pushouts = monomorphisms SSet.{u} :=
  sorry

lemma rlp_I_le_rlp_J : I.{u}.rlp ≤ J.{u}.rlp := by
  rw [← le_llp_iff_le_rlp, rlp_llp_of_isCardinalForSmallObjectArgument _ .aleph0,
    transfiniteCompositions_pushouts_coproducts]
  exact J_le_monomorphisms.trans (le_retracts _)

instance : HasFunctorialFactorization (trivialCofibrations SSet) (fibrations SSet) := by
  refine MorphismProperty.hasFunctorialFactorization_of_le (W₁ := J.rlp.llp)
    (W₂ := J.rlp) ?_ (by rfl)
  rw [trivialCofibrations, le_inf_iff,
    rlp_llp_of_isCardinalForSmallObjectArgument _ .aleph0]
  constructor
  · rw [cofibrations_eq]
    refine le_trans (monotone_retracts ?_) (retracts_le _)
    sorry -- use monotonicity
  · sorry -- J is mapped by the realization functor to trivial cofibrations in `TopCat`

-- the topological realization of a fibration of simplicial sets is a Serre fibration
instance {X Y : SSet.{0}} (f : X ⟶ Y) [Fibration f] :
    Fibration (toTop.map f) :=
  sorry

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
  rw [rlp_llp_of_isCardinalForSmallObjectArgument _ .aleph0, cofibrations_eq,
    transfiniteCompositions_pushouts_coproducts]
  apply retracts_le

end ModelCategory

open ModelCategory

instance : ModelCategory SSet.{0} where
  cm4a := sorry
  cm4b := sorry

end SSet
