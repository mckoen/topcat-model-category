import TopCatModelCategory.TopPackage
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.AlgebraicTopology.SingularSet

open HomotopicalAlgebra CategoryTheory MorphismProperty

namespace HomotopicalAlgebra

def packageTopCat : TopPackage.{0} TopCat.{0} where
  W := sorry
  I' := ofHoms (fun n ↦ SSet.toTop.map (SSet.boundaryInclusion.{0} n))
  J' := ⨆ n, ofHoms (fun i ↦ SSet.toTop.map (SSet.hornInclusion.{0} n i))
  S' := sorry
  fibration_is_trivial_iff' := sorry
  src_I_le_S' := sorry
  src_J_le_S' := sorry
  rlp_I'_le_rlp_J' := sorry
  preservesColimit' := sorry
  infiniteCompositions_le_W' := sorry
  hasTwoOutOfThreeProperty := sorry
  isStableUnderRetracts := sorry
  isSmall_I' := sorry
  isSmall_J' := sorry

end HomotopicalAlgebra

namespace TopCat

instance modelCategory : ModelCategory TopCat.{0} :=
  packageTopCat.modelCategoryCat

namespace ModelCategory

lemma weakEquivalence_iff_of_fibration {X Y : TopCat.{0}} (f : X ⟶ Y) [Fibration f] :
    (ofHoms (fun n ↦ SSet.toTop.map (SSet.boundaryInclusion.{0} n))).rlp f ↔
      WeakEquivalence f :=
  packageTopCat.I_rlp_iff_weakEquivalence_of_fibration f

open SSet

instance {X Y : TopCat.{0}} (f : X ⟶ Y) [Fibration f] [WeakEquivalence f] :
    HasLiftingProperty (toTop.map (boundaryInclusion n)) f := sorry

end ModelCategory

end TopCat
