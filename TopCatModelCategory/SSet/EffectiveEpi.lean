import TopCatModelCategory.SSet.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import TopCatModelCategory.ColimitsType

universe u

open CategoryTheory Limits

namespace SSet

variable {Y X : SSet.{u}} (p : Y ⟶ X) [Epi p]

namespace effectiveEpiStructOfEpi

variable {T : SSet.{u}} (f : Y ⟶ T)
  (hf : ∀ {Z : SSet.{u}} (g₁ g₂ : Z ⟶ Y),
    g₁ ≫ p = g₂ ≫ p → g₁ ≫ f = g₂ ≫ f)

lemma surjective_app {j : SimplexCategoryᵒᵖ} :
    Function.Surjective (p.app j) := by
  rw [← epi_iff_surjective]
  infer_instance

variable {p}

include hf in
lemma exists_img {j : SimplexCategoryᵒᵖ} (x : X.obj j) :
    ∃ (t : T.obj j), ∀ (y : Y.obj j), p.app _ y = x → f.app _ y = t := by
  obtain ⟨y₀, rfl⟩ := surjective_app p x
  refine ⟨f.app _ y₀, fun y hy ↦ ?_⟩
  obtain ⟨z, rfl, rfl⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback p p).map ((evaluation _ _).obj j))
    y y₀ hy
  exact congr_fun (congr_app (hf _ _ pullback.condition) j) z

noncomputable def descApp (j : SimplexCategoryᵒᵖ) : X.obj j ⟶ T.obj j :=
  fun x ↦ (exists_img f hf x).choose

lemma descApp_eq (j : SimplexCategoryᵒᵖ) (y : Y.obj j) :
    descApp f hf j (p.app _ y) = f.app _ y :=
  ((exists_img f hf (p.app _ y)).choose_spec _ rfl).symm

@[simps]
noncomputable def desc : X ⟶ T where
  app := descApp f hf
  naturality j₁ j₂ φ := by
    ext x
    obtain ⟨y, rfl⟩ := surjective_app p x
    dsimp
    rw [descApp_eq, ← FunctorToTypes.naturality, descApp_eq,
      FunctorToTypes.naturality]

end effectiveEpiStructOfEpi

open effectiveEpiStructOfEpi in
noncomputable def effectiveEpiStructOfEpi : EffectiveEpiStruct p where
  desc {T} f hf := desc f hf
  fac {T} f hf := by
    ext j y
    exact descApp_eq f hf y
  uniq {T} f hf l hl := by
    ext j x
    dsimp
    obtain ⟨y, rfl⟩ := surjective_app p x
    rw [descApp_eq, ← hl]
    dsimp

lemma effectiveEpi_of_epi : EffectiveEpi p where
  effectiveEpi := ⟨effectiveEpiStructOfEpi p⟩

end SSet
