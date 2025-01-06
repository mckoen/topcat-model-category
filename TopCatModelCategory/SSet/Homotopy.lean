import TopCatModelCategory.IsFibrant
import TopCatModelCategory.SSet.AnodyneExtensions

open HomotopicalAlgebra CategoryTheory Simplicial MonoidalCategory

universe u

namespace SSet

namespace Subcomplex

variable {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)

structure RelativeMorphism where
  map : X ⟶ Y
  le_preimage : A ≤ B.preimage map

namespace RelativeMorphism

variable {A B} (f g : RelativeMorphism A B)

lemma image_le : A.image f.map ≤ B := by
  simpa only [image_le_iff] using f.le_preimage

--structure Homotopy where
--  h : Δ[1] ⊗ X ⟶ Y
-- etc...

end RelativeMorphism

end Subcomplex


end SSet
