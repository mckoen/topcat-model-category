import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.CatCommSq

universe w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Pseudofunctor

section

variable {B C : Type*} [Bicategory B] [Bicategory C] (F : Pseudofunctor B C)

/-- More flexible variant of `mapId`. -/
def mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b) :
    F.map f ≅ 𝟙 _ :=
  F.map₂Iso (eqToIso (by rw [hf])) ≪≫ F.mapId _

lemma mapId'_eq_mapId (b : B) :
    F.mapId' (𝟙 b) rfl = F.mapId b := by
  simp [mapId']

/-- More flexible variant of `mapComp`. -/
def mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂) (h : fg = f ≫ g) :
    F.map fg ≅ F.map f ≫ F.map g :=
  F.map₂Iso (eqToIso (by rw [h])) ≪≫ F.mapComp f g

lemma mapComp'_eq_mapComp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    F.mapComp' f g _ rfl = F.mapComp f g := by
  simp [mapComp']

end

section

variable {B : Type u₁} [Category.{v₁} B]
  {F : Pseudofunctor (LocallyDiscrete B) Cat.{v₂, u₂}}

def catCommSqOfSq {X₁ X₂ Y₁ Y₂ : B} {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂} {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂}
    (sq : CommSq t l r b) :
    CatCommSq (F.map ⟨t⟩) (F.map ⟨l⟩) (F.map ⟨r⟩) (F.map ⟨b⟩) :=
  ⟨(F.mapComp ⟨t⟩ ⟨r⟩).symm ≪≫ F.mapComp' _ _ _ (by
    dsimp
    erw [← Quiver.Hom.comp_toLoc, ← Quiver.Hom.comp_toLoc]
    rw [sq.w])⟩

end

end Pseudofunctor

end CategoryTheory
