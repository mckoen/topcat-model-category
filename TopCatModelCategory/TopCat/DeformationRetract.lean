import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.Topology.UnitInterval
import TopCatModelCategory.TopCat.Monoidal

universe u

open CategoryTheory MonoidalCategory ChosenFiniteProducts

namespace TopCat

variable {X Y : TopCat.{u}}

structure DeformationRetract (f : X ⟶ Y) extends Retract X Y where
  h : Y ⊗ I ⟶ Y
  hi : toRetract.i ▷ _ ≫ h = fst _ _ ≫ toRetract.i := by aesop_cat
  h₀ : ι₀ ≫ h = r ≫ i := by aesop_cat
  h₁ : ι₁ ≫ h = 𝟙 Y := by aesop_cat

namespace DeformationRetract

variable (X) in
@[simps]
def id : DeformationRetract (𝟙 X) where
  i := 𝟙 X
  r := 𝟙 X
  h := fst _ _

end DeformationRetract

end TopCat
