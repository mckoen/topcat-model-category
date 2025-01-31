import TopCatModelCategory.SSet.NonDegenerateProdSimplex
import TopCatModelCategory.SSet.Monoidal

universe u

open CategoryTheory Simplicial MonoidalCategory

namespace SSet

namespace square

open ChosenFiniteProducts

noncomputable def ιTriangle₀ : (Δ[2] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  (yonedaEquiv _ _ ).symm (prodStandardSimplex.nonDegenerateEquiv₁ (q := 1) 0).1

noncomputable def ιTriangle₁ : (Δ[2] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  (yonedaEquiv _ _ ).symm (prodStandardSimplex.nonDegenerateEquiv₁ (q := 1) 1).1

noncomputable def diagonal : Δ[1] ⟶ Δ[1] ⊗ Δ[1] := lift (𝟙 _) (𝟙 _)

@[reassoc (attr := simp)]
lemma diagonal_fst : diagonal.{u} ≫ fst _ _ = 𝟙 _ := by simp [diagonal]

@[reassoc (attr := simp)]
lemma diagonal_snd : diagonal.{u} ≫ snd _ _ = 𝟙 _ := by simp [diagonal]

@[reassoc (attr := simp)]
lemma δ₀_diagonal :
    standardSimplex.map (SimplexCategory.δ 0) ≫ diagonal =
      const (prodStandardSimplex.obj₀Equiv.symm ⟨1, 1⟩) := by
  apply (yonedaEquiv _ _).injective
  apply Prod.ext <;> exact standardSimplex.obj₀Equiv.injective (by rfl)

@[reassoc (attr := simp)]
lemma δ₁_diagonal :
    standardSimplex.map (SimplexCategory.δ 1) ≫ diagonal =
      const (prodStandardSimplex.obj₀Equiv.symm ⟨0, 0⟩) := by
  apply (yonedaEquiv _ _).injective
  apply Prod.ext <;> exact standardSimplex.obj₀Equiv.injective (by rfl)

@[reassoc (attr := simp)]
lemma δ₀_ιTriangle₀ :
    standardSimplex.map (SimplexCategory.δ 0) ≫ square.ιTriangle₀ = ι₁ ≫ (β_ _ _).hom := by
  dsimp [ιTriangle₀]
  rw [standardSimplex.map_comp_yonedaEquiv_symm]
  apply (SSet.yonedaEquiv _ _).injective
  apply prodStandardSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma δ₁_ιTriangle₀ :
    standardSimplex.map (SimplexCategory.δ 1) ≫ square.ιTriangle₀ = diagonal := by
  dsimp [ιTriangle₀]
  rw [standardSimplex.map_comp_yonedaEquiv_symm]
  apply (SSet.yonedaEquiv _ _).injective
  apply prodStandardSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma δ₂_ιTriangle₀ : standardSimplex.map (SimplexCategory.δ 2) ≫ square.ιTriangle₀ = ι₀ := by
  dsimp [ιTriangle₀]
  rw [standardSimplex.map_comp_yonedaEquiv_symm]
  apply (SSet.yonedaEquiv _ _).injective
  apply prodStandardSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma δ₀_ιTriangle₁ : standardSimplex.map (SimplexCategory.δ 0) ≫ square.ιTriangle₁ = ι₁ := by
  dsimp [ιTriangle₁]
  rw [standardSimplex.map_comp_yonedaEquiv_symm]
  apply (SSet.yonedaEquiv _ _).injective
  apply prodStandardSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma δ₁_ιTriangle₁ :
    standardSimplex.map (SimplexCategory.δ 1) ≫ square.ιTriangle₁ = diagonal := by
  dsimp [ιTriangle₁]
  rw [standardSimplex.map_comp_yonedaEquiv_symm]
  apply (SSet.yonedaEquiv _ _).injective
  apply prodStandardSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma δ₂_ιTriangle₁ :
    standardSimplex.map (SimplexCategory.δ 2) ≫ square.ιTriangle₁ = ι₀ ≫ (β_ _ _).hom := by
  dsimp [ιTriangle₁]
  rw [standardSimplex.map_comp_yonedaEquiv_symm]
  apply (SSet.yonedaEquiv _ _).injective
  apply prodStandardSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

end square

end SSet
