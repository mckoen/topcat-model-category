import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.CatCommSq

universe w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory

open Bicategory

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
  (F : Pseudofunctor (LocallyDiscrete B) Cat.{v₂, u₂})

section

variable {X₁ X₂ Y₁ Y₂ : B} {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂} {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂}
  (sq : CommSq t l r b)

def isoMapOfSq : F.map ⟨t⟩ ≫ F.map ⟨r⟩ ≅ F.map ⟨l⟩ ≫ F.map ⟨b⟩ :=
  (F.mapComp ⟨t⟩ ⟨r⟩).symm ≪≫ F.mapComp' _ _ _ (by
    dsimp
    erw [← Quiver.Hom.comp_toLoc, ← Quiver.Hom.comp_toLoc]
    rw [sq.w])

@[simps]
def catCommSqOfSq :
    CatCommSq (F.map ⟨t⟩) (F.map ⟨l⟩) (F.map ⟨r⟩) (F.map ⟨b⟩) :=
  ⟨F.isoMapOfSq sq⟩

end

section

variable {X Y : B} (f : X ⟶ Y)

lemma isoMapOfSq_horiz_id :
    F.isoMapOfSq (t := 𝟙 _) (b := 𝟙 _) (l := f) (r := f) ⟨by simp⟩ =
        isoWhiskerRight (F.mapId ⟨X⟩) (F.map ⟨f⟩) ≪≫
        Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
        (isoWhiskerLeft (F.map ⟨f⟩) (F.mapId ⟨Y⟩)).symm := by
  ext
  dsimp [isoMapOfSq]
  sorry

end


section

variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : B} {t : X₁ ⟶ Y₁} {t' : Y₁ ⟶ Z₁}
    {l : X₁ ⟶ X₂} {m : Y₁ ⟶ Y₂} {r : Z₁ ⟶ Z₂}
    {b : X₂ ⟶ Y₂} {b' : Y₂ ⟶ Z₂}
    (sq : CommSq t l m b) (sq' : CommSq t' m r b')
    {t'' : X₁ ⟶ Z₁} {b'' : X₂ ⟶ Z₂}
    (ht : t ≫ t' = t'') (hb : b ≫ b' = b'')

include ht hb sq sq'

lemma _root_.CategoryTheory.CommSq.horiz_comp' : CommSq t'' l r b'' := by
  subst ht hb
  exact sq.horiz_comp sq'

lemma isoMapOfSq_horiz_comp :
    F.isoMapOfSq (sq.horiz_comp' sq' ht hb) =
      isoWhiskerRight (F.mapComp' ⟨t⟩ ⟨t'⟩ ⟨t''⟩ (by rw [← ht]; rfl)) (F.map ⟨r⟩) ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft (F.map ⟨t⟩) (F.isoMapOfSq sq') ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.isoMapOfSq sq) (F.map ⟨b'⟩) ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft (F.map ⟨l⟩)
        ((F.mapComp' ⟨b⟩ ⟨b'⟩ ⟨b''⟩ (by rw [← hb]; rfl)).symm) := by
  subst ht hb
  ext
  dsimp [isoMapOfSq]
  simp
  sorry

end

end

end Pseudofunctor

end CategoryTheory
