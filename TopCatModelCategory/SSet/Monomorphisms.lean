import TopCatModelCategory.SSet.CategoryWithFibrations
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

universe u

open CategoryTheory MorphismProperty

namespace SSet

namespace modelCategory

lemma transfiniteCompositions_pushouts_coproducts :
    transfiniteCompositions.{u} I.coproducts.{u}.pushouts = monomorphisms SSet.{u} :=
  sorry

lemma I_rlp_eq_monomorphisms_rlp : I.{u}.rlp = (monomorphisms SSet.{u}).rlp := by
  sorry

end modelCategory

end SSet
