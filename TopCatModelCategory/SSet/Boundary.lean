import TopCatModelCategory.SSet.Subcomplex
import Mathlib.Data.Finite.Card

universe u

namespace SSet

open Simplicial

namespace standardSimplex

variable {n : ℕ}

@[ext]
lemma ext {j : SimplexCategoryᵒᵖ} {x y : (Δ[n] : SSet.{u}).obj j}
    (h : objEquiv _ _ x = objEquiv _ _ y) : x = y :=
  (objEquiv _ _).injective h

@[simps]
def face (S : Set (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex where
  obj U := setOf (fun f ↦ Set.range ((objEquiv _ _) f).toOrderHom ⊆ S)
  map := by
    rintro _ _ _ _ hx _ ⟨j, rfl⟩
    exact hx (by aesop)

lemma face_inter_face (S₁ S₂ : Set (Fin (n + 1))) :
    face S₁ ⊓ face S₂ = face (S₁ ⊓ S₂) := by
  aesop

def faceRepresentableBy (S : Set (Fin (n + 1)))
    (m : ℕ) (e : Fin (m + 1) ≃o S) :
    (face S : SSet.{u}).RepresentableBy (.mk m) where
  homEquiv {j} :=
    { toFun f := ⟨objMk ((OrderHom.Subtype.val S).comp
          (e.toOrderEmbedding.toOrderHom.comp f.toOrderHom)), fun _ ↦ by aesop⟩
      invFun := fun ⟨x, hx⟩ ↦ SimplexCategory.Hom.mk
        { toFun i := e.symm ⟨(objEquiv _ _ x).toOrderHom i, hx (Set.mem_range_self i)⟩
          monotone' i₁ i₂ h := e.symm.monotone (by
            simp only [Subtype.mk_le_mk]
            exact OrderHom.monotone _ h) }
      left_inv f := by
        ext i : 3
        apply e.symm_apply_apply
      right_inv := fun ⟨x, hx⟩ ↦ by
        dsimp
        ext i : 5
        exact congr_arg Subtype.val
          (e.apply_symm_apply ⟨(objEquiv _ _ x).toOrderHom i, _⟩) }
  homEquiv_comp f g := by aesop

end standardSimplex

lemma subcomplexBoundary_eq_iSup :
    subcomplexBoundary.{u} n = ⨆ (i : Fin (n + 1)), standardSimplex.face {i}ᶜ := by
  ext
  simp [standardSimplex.face, subcomplexBoundary, Function.Surjective]
  tauto

lemma subcomplexHorn_eq_iSup (i : Fin (n + 1)) :
    subcomplexHorn.{u} n i =
      ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), standardSimplex.face {j.1}ᶜ := by
  ext m j
  simp [standardSimplex.face, subcomplexHorn]
  change ¬ _ ↔ _
  simp [Set.eq_univ_iff_forall]
  rfl

end SSet
