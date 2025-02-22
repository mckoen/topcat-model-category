import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Closed.Monoidal
import TopCatModelCategory.MonoidalClosed
import TopCatModelCategory.SSet.Basic
import TopCatModelCategory.SSet.StandardSimplex

universe u

open CategoryTheory MonoidalCategory Simplicial Opposite Limits
  ChosenFiniteProducts

namespace SSet

section

variable {X : SSet.{u}}

noncomputable abbrev ι₀ {X : SSet.{u}} : X ⟶ X ⊗ Δ[1] :=
  lift (𝟙 X) (const (standardSimplex.obj₀Equiv.{u}.symm 0))

@[reassoc (attr := simp)]
lemma ι₀_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₀ ≫ f ▷ _ = f ≫ ι₀ := rfl

@[reassoc]
lemma ι₀_fst (X : SSet.{u}) : ι₀ ≫ fst X _ = 𝟙 X := rfl

@[simp]
lemma ι₀_app_fst {X : SSet.{u}} {m} (x : X.obj m) : (ι₀.app _ x).1 = x := rfl

noncomputable abbrev ι₁ {X : SSet.{u}} : X ⟶ X ⊗ Δ[1] :=
  lift (𝟙 X) (const (standardSimplex.obj₀Equiv.{u}.symm 1))

@[reassoc]
lemma ι₁_fst (X : SSet.{u}) : ι₁ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma ι₁_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₁ ≫ f ▷ _ = f ≫ ι₁ := rfl

@[simp]
lemma ι₁_app_fst {X : SSet.{u}} {m} (x : X.obj m) : (ι₁.app _ x).1 = x := rfl

end

namespace standardSimplex

variable (X) {Y : SSet.{u}}

def isTerminalObj₀ : IsTerminal (Δ[0] : SSet.{u}) :=
  IsTerminal.ofUniqueHom (fun _ ↦ SSet.const (obj₀Equiv.symm 0)) (fun _ _ ↦ by ext; simp)

noncomputable def leftUnitor : Δ[0] ⊗ X ≅ X where
  hom := snd _ _
  inv := lift (isTerminalObj₀.from _) (𝟙 X)

@[reassoc (attr := simp)]
lemma leftUnitor_inv_snd : (leftUnitor X).inv ≫ snd _ _ = 𝟙 _ := rfl

variable {X} in
@[reassoc (attr := simp)]
lemma leftUnitor_inv_naturality (f : X ⟶ Y) :
    (leftUnitor X).inv ≫ _ ◁ f = f ≫ (leftUnitor Y).inv := rfl

variable {X} in
@[reassoc (attr := simp)]
lemma leftUnitor_hom_naturality (f : X ⟶ Y) :
    _ ◁ f  ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := rfl

@[reassoc (attr := simp)]
lemma leftUnitor_inv_map_δ_zero :
    (standardSimplex.leftUnitor X).inv ≫ standardSimplex.map (SimplexCategory.δ 0) ▷ X =
      ι₁ ≫ (β_ _ _).hom := rfl

@[reassoc (attr := simp)]
lemma leftUnitor_inv_map_δ_one :
    (standardSimplex.leftUnitor X).inv ≫ standardSimplex.map (SimplexCategory.δ 1) ▷ X =
      ι₀ ≫ (β_ _ _).hom := rfl

@[reassoc]
lemma ι₀_standardSimplex_zero :
    ι₀ = standardSimplex.map (SimplexCategory.δ 1) ≫ (standardSimplex.leftUnitor Δ[1]).inv := by
  ext : 1
  all_goals exact (yonedaEquiv _ _).injective (by ext i; fin_cases i; rfl)

@[reassoc]
lemma ι₁_standardSimplex_zero :
    ι₁ = standardSimplex.map (SimplexCategory.δ 0) ≫ (standardSimplex.leftUnitor Δ[1]).inv := by
  ext : 1
  all_goals exact (yonedaEquiv _ _).injective (by ext i; fin_cases i; rfl)

noncomputable def rightUnitor : X ⊗ Δ[0] ≅ X where
  hom := fst _ _
  inv := lift (𝟙 X) (isTerminalObj₀.from _)

@[reassoc (attr := simp)]
lemma rightUnitor_inv_fst : (rightUnitor X).inv ≫ fst _ _ = 𝟙 _ := rfl

variable {X} in
@[reassoc (attr := simp)]
lemma rightUnitor_inv_naturality (f : X ⟶ Y) :
    (rightUnitor X).inv ≫ f ▷ _ = f ≫ (rightUnitor Y).inv := rfl

variable {X} in
@[reassoc (attr := simp)]
lemma rightUnitor_hom_naturality (f : X ⟶ Y) :
    f ▷ _ ≫  (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_inv_map_δ_zero :
    (standardSimplex.rightUnitor X).inv ≫ X ◁ standardSimplex.map (SimplexCategory.δ 0) =
      ι₁ := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_inv_map_δ_one :
    (standardSimplex.rightUnitor X).inv ≫ X ◁ standardSimplex.map (SimplexCategory.δ 1) =
      ι₀ := rfl

end standardSimplex

instance : MonoidalClosed (SSet.{u}) :=
  inferInstanceAs (MonoidalClosed (SimplexCategoryᵒᵖ ⥤ Type u))

variable {X Y : SSet.{u}}

noncomputable def ihom₀Equiv : ((ihom X).obj Y) _[0] ≃ (X ⟶ Y) :=
  (yonedaEquiv _ _).symm.trans
    (((ihom.adjunction X).homEquiv Δ[0] Y).symm.trans
      (Iso.homFromEquiv (standardSimplex.rightUnitor X)))

lemma ihom₀Equiv_symm_comp {Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ihom₀Equiv.symm (f ≫ g) =
      ((MonoidalClosed.pre f).app Z).app (op [0]) (ihom₀Equiv.symm g) := by
  apply (yonedaEquiv _ _).symm.injective
  dsimp [ihom₀Equiv]
  rw [Equiv.symm_apply_apply, ← yonedaEquiv_symm_comp, Equiv.symm_apply_apply]
  rfl

lemma yonedaEquiv_fst {n : ℕ} (f : Δ[n] ⟶ X ⊗ Y) :
    (yonedaEquiv _ _ f).1 = yonedaEquiv _ _ (f ≫ fst _ _) := rfl

lemma yonedaEquiv_snd {n : ℕ} (f : Δ[n] ⟶ X ⊗ Y) :
    (yonedaEquiv _ _ f).2 = yonedaEquiv _ _ (f ≫ snd _ _) := rfl

end SSet
