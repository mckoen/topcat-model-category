import TopCatModelCategory.TopPackage
import TopCatModelCategory.TopCat.W
import TopCatModelCategory.SSet.Finite
import TopCatModelCategory.SSet.Skeleton
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SingularSet

open HomotopicalAlgebra CategoryTheory MorphismProperty

namespace HomotopicalAlgebra

def packageTopCat : TopPackage.{0} TopCat.{0} where
  I' := ofHoms (fun n ↦ SSet.toTop.map (SSet.boundary.{0} n).ι)
  J' := ⨆ n, ofHoms (fun i ↦ SSet.toTop.map (SSet.horn.{0} (n + 1) i).ι)
  S' := Set.range (fun (X : {(X : SSet.{0}) | SSet.IsFinite X}) ↦ SSet.toTop.obj X)
  src_I_le_S' := by
    rintro _ _ _ ⟨i⟩
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop]
    exact ⟨_, inferInstance, rfl⟩
  src_J_le_S' := by
    rintro _ _ _ hf
    simp only [iSup_iff] at hf
    obtain ⟨_, ⟨_⟩⟩ := hf
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop]
    exact ⟨_, inferInstance, rfl⟩
  rlp_I'_le_rlp_J' := by
    intro _ _ f hf _ _ g hg
    simp only [iSup_iff] at hg
    obtain ⟨n, ⟨i⟩⟩ := hg
    rw [sSetTopAdj.hasLiftingProperty_iff]
    have : SSet.modelCategoryQuillen.I.rlp (TopCat.toSSet.map f) := by
      rintro _ _ _ ⟨n⟩
      rw [← sSetTopAdj.hasLiftingProperty_iff]
      apply hf
      constructor
    rw [SSet.modelCategoryQuillen.I_rlp_eq_monomorphisms_rlp] at this
    exact this _ (monomorphisms.infer_property _)
  -- the next two sorries were formalised in Lean 3 by Reid Barton
  preservesColimit' := sorry
  infiniteCompositions_le_W' := sorry
  -- this is the key property
  fibration_is_trivial_iff' := sorry

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

lemma trivialCofibrations_eq_llp_rlp :
    trivialCofibrations TopCat =
      (⨆ n, ofHoms (fun i ↦ SSet.toTop.map (SSet.horn.{0} (n + 1) i).ι)).rlp.llp :=
  packageTopCat.trivialCofibrations_eq_llp_rlp_J

end ModelCategory

end TopCat
