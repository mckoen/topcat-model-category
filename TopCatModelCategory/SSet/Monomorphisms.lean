import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.ULift
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

universe w v u

open CategoryTheory MorphismProperty Limits

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

@[simp]
lemma rlp_transfiniteCompositions (W : MorphismProperty C) :
    (transfiniteCompositions.{w} W).rlp = W.rlp := by
  apply le_antisymm
  · exact antitone_rlp W.le_transfiniteCompositions
  · rw [← le_llp_iff_le_rlp]
    exact transfiniteCompositions_le_llp_rlp W

instance [(monomorphisms C).IsStableUnderCobaseChange] [HasPushouts C]
    [HasPullbacks C] (J : Type*) [Category J] :
    (monomorphisms (J ⥤ C)).IsStableUnderCobaseChange := by
  rw [← functorCategory_monomorphisms]
  infer_instance

end CategoryTheory.MorphismProperty

namespace SSet

instance : IsStableUnderTransfiniteComposition.{u} (monomorphisms (SSet.{u})) where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    change (monomorphisms (_ ⥤ _)).IsStableUnderTransfiniteCompositionOfShape _
    infer_instance

instance : IsStableUnderCobaseChange (monomorphisms (SSet.{u})) :=
  inferInstanceAs (monomorphisms (_ ⥤ _)).IsStableUnderCobaseChange

instance : IsStableUnderCoproducts.{u} (monomorphisms (SSet.{u})) := sorry

namespace modelCategoryQuillen

def transfiniteCompositionMonomorphisms {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    (coproducts.{u} I).pushouts.TransfiniteCompositionOfShape ℕ i := by
  sorry

lemma transfiniteCompositions_pushouts_coproducts :
    transfiniteCompositions.{u} (coproducts.{u} I).pushouts = monomorphisms SSet.{u} := by
  apply le_antisymm
  · rw [transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact I_le_monomorphisms
  · intro _ _ i (_ : Mono i)
    apply transfiniteCompositionsOfShape_le_transfiniteCompositions _ (ULift ℕ)
    exact ⟨(transfiniteCompositionMonomorphisms i).ofOrderIso (orderIsoULift.{u} ℕ).symm⟩

lemma I_rlp_eq_monomorphisms_rlp : I.{u}.rlp = (monomorphisms SSet.{u}).rlp := by
  apply le_antisymm
  · simp only [← transfiniteCompositions_pushouts_coproducts,
      rlp_transfiniteCompositions, rlp_pushouts, rlp_coproducts, le_refl]
  · exact MorphismProperty.antitone_rlp I_le_monomorphisms

end modelCategoryQuillen

end SSet
