import TopCatModelCategory.SSet.Subcomplex
import TopCatModelCategory.SSet.StandardSimplex

universe u

namespace SSet

open Simplicial

lemma subcomplexBoundary_eq_iSup :
    subcomplexBoundary.{u} n = ⨆ (i : Fin (n + 1)), standardSimplex.face {i}ᶜ := by
  ext
  simp [standardSimplex.face, subcomplexBoundary, Function.Surjective]
  tauto

end SSet
