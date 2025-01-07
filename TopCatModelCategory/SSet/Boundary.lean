import TopCatModelCategory.SSet.Subcomplex
import TopCatModelCategory.SSet.StandardSimplex
import TopCatModelCategory.SSet.HasDimensionLT

universe u

open Simplicial Opposite

namespace SSet

lemma subcomplexBoundary_eq_iSup :
    subcomplexBoundary.{u} n = ⨆ (i : Fin (n + 1)), standardSimplex.face {i}ᶜ := by
  ext
  simp [standardSimplex.face, subcomplexBoundary, Function.Surjective]
  tauto

lemma face_le_subcomplexBoundary (i : Fin (n + 1)) :
    standardSimplex.face.{u} {i}ᶜ ≤ subcomplexBoundary n := by
  rw [subcomplexBoundary_eq_iSup]
  exact le_iSup (fun (i : Fin (n +1)) ↦ standardSimplex.face {i}ᶜ) i

lemma non_mem_subcomplexBoundary (n : ℕ):
    standardSimplex.objMk .id ∉ (subcomplexBoundary.{u} n).obj (op [n]) := by
  simp only [subcomplexBoundary_eq_iSup, CategoryTheory.GrothendieckTopology.iSup_obj,
    Set.iSup_eq_iUnion, Set.mem_iUnion, not_exists]
  intro i hi
  simpa using @hi i ⟨i, rfl⟩

lemma subcomplexBoundary_obj_eq_top (m n : ℕ) (h : m < n) :
    (subcomplexBoundary.{u} n).obj (op [m]) = ⊤ := by
  ext x
  obtain ⟨f, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective x
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  obtain _ | n := n
  · simp at h
  · obtain ⟨i, q, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f (fun hf ↦ by
      rw [← SimplexCategory.epi_iff_surjective] at hf
      have := SimplexCategory.le_of_epi (f := f) inferInstance
      omega)
    apply face_le_subcomplexBoundary i
    rintro _ ⟨x, rfl⟩
    apply Fin.succAbove_ne

instance : HasDimensionLT (subcomplexBoundary.{u} n) n := by
  sorry

namespace standardSimplex

variable {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)

lemma subcomplex_le_boundary_iff :
    A ≤ subcomplexBoundary n ↔ A ≠ ⊤ := by
  constructor
  · rintro h rfl
    exact non_mem_subcomplexBoundary.{u} n (h _ (by simp))
  · intro h
    -- * show A is of dimension < n because it does not contain the "𝟙 [n]"` simplex
    -- * generalize `Subcomplex.eq_top_iff_of_hasDimensionLT`
    --   to an inclusion between two subcomplexes
    -- * use `subcomplexBoundary_obj_eq_top`
    -- note: generalize also `eq_top_iff_contains_nonDegenerate` as a
    -- `le_iff_contains_nonDegenerate` lemma
    sorry

end standardSimplex

end SSet
