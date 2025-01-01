import TopcatModelCategory.SSet.Subobject

universe u

namespace SSet

open Simplicial

namespace standardSimplex

variable {n : ℕ} (S : Set (Fin (n + 1)))

def face : (Δ[n] : SSet.{u}).Subobject where
  obj U := setOf (fun ⟨f⟩ ↦ Set.range f.toOrderHom ⊆ S)
  map := by
    rintro _ _ _ _ hx _ ⟨j, rfl⟩
    exact hx (by simp)

end standardSimplex

lemma subobjectBoundary_eq_iSup :
    subobjectBoundary.{u} n = ⨆ (i : Fin (n + 1)), standardSimplex.face {i}ᶜ := by
  ext
  simp [standardSimplex.face, subobjectBoundary, Function.Surjective]
  tauto

end SSet
