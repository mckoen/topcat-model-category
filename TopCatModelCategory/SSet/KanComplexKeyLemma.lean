import TopCatModelCategory.SSet.KanComplexW

universe u

open HomotopicalAlgebra CategoryTheory
namespace SSet

open modelCategoryQuillen

namespace KanComplex

lemma weakEquivalence_iff_of_fibration {X Y : SSet.{0}} (p : X ⟶ Y)
    [IsFibrant X] [IsFibrant Y] [Fibration p] :
    I.rlp p ↔ KanComplex.W p :=
  sorry

end KanComplex

end SSet
