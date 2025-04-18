import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.Topology.UnitInterval
import TopCatModelCategory.TopCat.Monoidal

universe u

open CategoryTheory MonoidalCategory ChosenFiniteProducts

namespace TopCat

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

structure DeformationRetract extends Retract X Y where
  h : Y ⊗ I ⟶ Y
  hi : toRetract.i ▷ _ ≫ h = fst _ _ ≫ toRetract.i
  h₀ : ι₀ ≫ h = r ≫ i
  h₁ : ι₁ ≫ h = 𝟙 Y

end TopCat
