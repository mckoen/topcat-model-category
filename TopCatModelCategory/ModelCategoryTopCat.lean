import TopCatModelCategory.TopPackage
import TopCatModelCategory.TopCat.W
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SingularSet

open HomotopicalAlgebra CategoryTheory MorphismProperty

namespace HomotopicalAlgebra

def packageTopCat : TopPackage.{0} TopCat.{0} where
  I' := ofHoms (fun n ↦ SSet.toTop.map (SSet.boundary.{0} n).ι)
  J' := ⨆ n, ofHoms (fun i ↦ SSet.toTop.map (SSet.horn.{0} (n + 1) i).ι)
  S' := sorry
  src_I_le_S' := sorry
  src_J_le_S' := sorry
  rlp_I'_le_rlp_J' := sorry
  fibration_is_trivial_iff' := sorry
  preservesColimit' := sorry
  infiniteCompositions_le_W' := sorry

end HomotopicalAlgebra

namespace TopCat

instance modelCategory : ModelCategory TopCat.{0} :=
  packageTopCat.modelCategoryCat

namespace ModelCategory

lemma weakEquivalence_iff_of_fibration {X Y : TopCat.{0}} (f : X ⟶ Y) [Fibration f] :
    (ofHoms (fun n ↦ SSet.toTop.map (SSet.boundary.{0} n).ι)).rlp f ↔
      WeakEquivalence f :=
  packageTopCat.I_rlp_iff_weakEquivalence_of_fibration f

open SSet

instance (n : ℕ) : Cofibration (toTop.map (boundary n).ι) := by
  rw [HomotopicalAlgebra.cofibration_iff]
  apply MorphismProperty.le_llp_rlp
  constructor

end ModelCategory

end TopCat
