import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Closed.Monoidal

universe u

open CategoryTheory MonoidalCategory Simplicial Opposite

namespace SSet

instance : MonoidalClosed (SSet.{u}) := sorry

variable (X : SSet.{u})

instance : (tensorLeft X).IsLeftAdjoint := sorry
instance : (tensorRight X).IsLeftAdjoint := sorry

instance : (ihom X).IsRightAdjoint := sorry

variable {X} {Y : SSet.{u}}

def ihom₀Equiv : ((ihom X).obj Y) _[0] ≃ (X ⟶ Y) := sorry

lemma ihom₀Equiv_symm_comp {Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ihom₀Equiv.symm (f ≫ g) =
      ((MonoidalClosed.pre f).app Z).app (op [0]) (ihom₀Equiv.symm g) := sorry

end SSet
