import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.ULift
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

universe w v u

open CategoryTheory MorphismProperty

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

@[simp]
lemma rlp_transfiniteCompositions :
    (transfiniteCompositions.{w} W).rlp = W.rlp := by
  apply le_antisymm
  · exact antitone_rlp W.le_transfiniteCompositions
  · rw [← le_llp_iff_le_rlp]
    exact transfiniteCompositions_le_llp_rlp W

end CategoryTheory.MorphismProperty

namespace SSet

instance : IsStableUnderTransfiniteComposition.{u} (monomorphisms (SSet.{u})) := sorry
instance : IsStableUnderCobaseChange (monomorphisms (SSet.{u})) := sorry
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
