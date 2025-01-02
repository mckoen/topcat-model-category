import TopCatModelCategory.TopPackage
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.AlgebraicTopology.SingularSet

open HomotopicalAlgebra CategoryTheory

namespace HomotopicalAlgebra

open MorphismProperty

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
  packageTopCat.modelCategory

end TopCat
