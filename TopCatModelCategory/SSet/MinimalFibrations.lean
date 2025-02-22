import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.SSet.Degenerate

universe u

open CategoryTheory HomotopicalAlgebra Simplicial MonoidalCategory
  ChosenFiniteProducts Category

namespace SSet

variable {E B : SSet.{u}} (p : E ⟶ B)

structure SimplexOverRel {n : ℕ} (x y : E _[n]) where
  h : Δ[n] ⊗ Δ[1] ⟶ E
  h₀ : ι₀ ≫ h = (yonedaEquiv _ _).symm x
  h₁ : ι₁ ≫ h = (yonedaEquiv _ _).symm y
  π : Δ[n] ⟶ B
  d : ∂Δ[n] ⟶ E
  hπ : h ≫ p = fst _ _ ≫ π
  hd : (subcomplexBoundary.{u} n).ι ▷ Δ[1] ≫ h = fst _ _ ≫ d

class MinimalFibration extends Fibration p : Prop where
  minimal {n : ℕ} {x y : E _[n]} (rel : SimplexOverRel p x y) : x = y

instance : MinimalFibration (𝟙 B) where
  minimal {n x y} rel := by
    apply (yonedaEquiv _ _).symm.injective
    simp only [← rel.h₀, ← rel.h₁, ← cancel_mono (𝟙 B), assoc, rel.hπ,
      lift_fst_assoc, id_comp]

lemma eq_of_degenerate {X : SSet.{u}} {n : ℕ} {x y : X _[n + 1]} (hx : x ∈ X.Degenerate (n + 1))
    (hy : y ∈ X.Degenerate (n + 1))
    (h : ∀ (i : Fin (n + 2)), X.δ i x = X.δ i y) : x = y := by
  simp only [degenerate_eq_iUnion_range_σ, Set.iSup_eq_iUnion, Set.mem_iUnion,
    Set.mem_range] at hx hy
  obtain ⟨p, x', hx'⟩ := hx
  obtain ⟨q, y', hy'⟩ := hy
  have hx : x' = X.δ p.castSucc x := by rw [← hx', δ_comp_σ_self_apply]
  have hy : y' = X.δ q.castSucc y := by rw [← hy', δ_comp_σ_self_apply]
  wlog hpq : p < q
  · simp only [not_lt] at hpq
    obtain hpq | rfl := hpq.lt_or_eq
    · exact (this (fun i ↦ (h i).symm) q y' hy' p x' hx' hy hx hpq).symm
    · rw [← hx', ← hy', hx, hy, h]
  sorry

namespace SimplexOverRel

attribute [reassoc] h₀ h₁ hπ hd

variable {p} {n : ℕ} {x y : E _[n]} (rel : SimplexOverRel p x y)

include rel in
lemma eq_of_degenerate (hx : x ∈ E.Degenerate n) (hy : y ∈ E.Degenerate n) :
    x = y := by
  obtain _ | n := n
  · simp at hx
  have h₀ := (subcomplexBoundary.{u} (n + 1)).ι ≫= rel.h₀
  have h₁ := (subcomplexBoundary.{u} (n + 1)).ι ≫= rel.h₁
  erw [← ι₀_comp_assoc, rel.hd, ι₀_fst_assoc] at h₀
  erw [← ι₁_comp_assoc, rel.hd, ι₁_fst_assoc] at h₁
  apply eq_of_degenerate hx hy (fun i ↦ ?_)
  have := subcomplexBoundary.ι i ≫= (h₀.symm.trans h₁)
  rw [subcomplexBoundary.ι_ι_assoc, subcomplexBoundary.ι_ι_assoc,
    ← yonedaEquiv_symm_map, ← yonedaEquiv_symm_map] at this
  exact (yonedaEquiv _ _).symm.injective this

end SimplexOverRel

end SSet
