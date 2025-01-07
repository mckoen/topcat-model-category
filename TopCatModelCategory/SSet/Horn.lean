import TopCatModelCategory.SSet.Boundary

universe u

namespace SSet

open Simplicial

lemma subcomplexHorn_eq_iSup (i : Fin (n + 1)) :
    subcomplexHorn.{u} n i =
      ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), standardSimplex.face {j.1}ᶜ := by
  ext m j
  simp [standardSimplex.face, subcomplexHorn]
  change ¬ _ ↔ _
  simp [Set.eq_univ_iff_forall]
  rfl

end SSet
