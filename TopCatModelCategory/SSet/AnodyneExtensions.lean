import TopCatModelCategory.SSet.CategoryWithFibrations
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

open HomotopicalAlgebra CategoryTheory Limits SSet.ModelCategory

universe u

namespace SSet

def anodyneExtensions : MorphismProperty SSet.{u} :=
  (fibrations _).llp

namespace anodyneExtensions

lemma subcomplexHorn_ι_mem (n : ℕ) (i : Fin (n + 1)) :
    anodyneExtensions (subcomplexHorn.{u} n i).ι := by
  apply MorphismProperty.le_rlp_llp
  simp only [J, MorphismProperty.iSup_iff]
  exact ⟨n, ⟨i⟩⟩

lemma subcomplex_unionProd_face_ι_mem {X : SSet.{u}} (Y : X.Subcomplex) (i : Fin 2) :
    anodyneExtensions (Subcomplex.unionProd (standardSimplex.face {i})
      (subcomplexBoundary n)).ι := sorry

lemma subcomplex_unionProd_face_boundary_ι_mem (n : ℕ) (i : Fin 2) :
    anodyneExtensions (Subcomplex.unionProd (standardSimplex.face {i})
      (subcomplexBoundary n)).ι := by
  sorry -- `subcomplex_unionProd_face_ι_mem` and the skeleton filtration

end anodyneExtensions
