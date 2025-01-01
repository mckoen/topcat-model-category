import TopcatModelCategory.SSet.Subobject
import Mathlib.Data.Finite.Card

universe u

namespace SSet

open Simplicial

namespace standardSimplex

variable {n : ℕ}

@[simps]
def face (S : Set (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subobject where
  obj U := setOf (fun ⟨f⟩ ↦ Set.range f.toOrderHom ⊆ S)
  map := by
    rintro _ _ _ _ hx _ ⟨j, rfl⟩
    exact hx (by simp)

lemma face_inter_face (S₁ S₂ : Set (Fin (n + 1))) :
    face S₁ ⊓ face S₂ = face (S₁ ⊓ S₂) := by
  aesop

def faceRepresentableBy (S : Set (Fin (n + 1)))
    (m : ℕ) (e : Fin (m + 1) ≃o S) :
    (face S : SSet.{u}).RepresentableBy (.mk m) where
  homEquiv {j} :=
    { toFun f := ⟨objMk ((OrderHom.Subtype.val S).comp
          (e.toOrderEmbedding.toOrderHom.comp f.toOrderHom)), fun _ ↦ by aesop⟩
      invFun := sorry
      left_inv := sorry
      right_inv := sorry }
  homEquiv_comp f g := by aesop

end standardSimplex

lemma subobjectBoundary_eq_iSup :
    subobjectBoundary.{u} n = ⨆ (i : Fin (n + 1)), standardSimplex.face {i}ᶜ := by
  ext
  simp [standardSimplex.face, subobjectBoundary, Function.Surjective]
  tauto

end SSet
