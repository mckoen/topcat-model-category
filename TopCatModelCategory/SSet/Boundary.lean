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

namespace standardSimplex

variable {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)

lemma subcomplex_hasDimensionLT_of_neq_top (h : A ≠ ⊤) :
    HasDimensionLT A n where
  degenerate_eq_top i hi := by
    ext ⟨a, ha⟩
    rw [A.mem_degenerate_iff]
    simp
    obtain hi | rfl := hi.lt_or_eq
    · simp [Δ[n].degenerate_eq_top_of_hasDimensionLT (n + 1) i (by omega)]
    · rw [mem_degenerate_iff_non_mem_nondegenerate, non_degenerate_top_dim]
      rintro rfl
      apply h
      ext ⟨m⟩ x
      obtain ⟨f, rfl⟩ := (objEquiv _ _).symm.surjective x
      simpa using A.map f.op ha

lemma subcomplex_le_boundary_iff :
    A ≤ subcomplexBoundary n ↔ A ≠ ⊤ := by
  constructor
  · rintro h rfl
    exact non_mem_subcomplexBoundary.{u} n (h _ (by simp))
  · intro h
    have := subcomplex_hasDimensionLT_of_neq_top _ h
    rw [Subcomplex.le_iff_contains_nonDegenerate]
    rintro m ⟨x, h₁⟩ h₂
    dsimp at h₂ ⊢
    by_cases h₃ : m < n
    · simp [subcomplexBoundary_obj_eq_top m n (by simpa using h₃)]
    · simp only [not_lt] at h₃
      replace h₁ := (A.mem_non_degenerate_iff ⟨x, h₂⟩).2 h₁
      rw [nondegenerate_eq_bot_of_hasDimensionLT _ _ _ h₃] at h₁
      simp at h₁

instance : HasDimensionLT (subcomplexBoundary.{u} n) n := by
  apply subcomplex_hasDimensionLT_of_neq_top
  intro h
  simpa [h] using non_mem_subcomplexBoundary.{u} n

end standardSimplex

end SSet
