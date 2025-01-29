import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Closed.Monoidal

universe u

open CategoryTheory MonoidalCategory

namespace SSet

instance : MonoidalClosed (SSet.{u}) := sorry

variable (X : SSet.{u})

instance : (tensorLeft X).IsLeftAdjoint := sorry
instance : (tensorRight X).IsLeftAdjoint := sorry

instance : (ihom X).IsRightAdjoint := sorry

end SSet
