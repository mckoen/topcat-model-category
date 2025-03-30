import TopCatModelCategory.SSet.Monoidal
import Mathlib.CategoryTheory.Retract

universe u

open CategoryTheory Category MonoidalCategory Simplicial
  ChosenFiniteProducts

namespace SSet

variable (X Y : SSet.{u})

structure DeformationRetract extends Retract X Y where
  h : Y ⊗ Δ[1] ⟶ Y
  hi : toRetract.i ▷ _ ≫ h = fst _ _ ≫ toRetract.i
  h₀ : ι₀ ≫ h = r ≫ i
  h₁ : ι₁ ≫ h = 𝟙 Y

namespace DeformationRetract

attribute [reassoc (attr := simp)] hi h₁

variable {X Y} (d : DeformationRetract X Y)

@[reassoc (attr := simp)]
lemma i_ι₀ : d.i ≫ ι₀ ≫ d.h = d.i := by
  simpa only [ι₀_comp_assoc, lift_fst_assoc, id_comp] using ι₀ ≫= d.hi

end DeformationRetract

variable {X Y} {B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)

structure RelativeDeformationRetract extends DeformationRetract X Y where
  wr : r ≫ p = q
  wh : h ≫ q = fst _ _ ≫ q

namespace RelativeDeformationRetract

variable {p q} (d : RelativeDeformationRetract p q)

attribute [reassoc (attr := simp)] wr wh

@[reassoc (attr := simp)]
lemma wi : d.i ≫ q = p := by
  simp only [← d.wr, d.retract_assoc]

@[simps]
def retractArrow : RetractArrow p q where
  i := Arrow.homMk d.i (𝟙 B)
  r := Arrow.homMk d.r (𝟙 B)

end RelativeDeformationRetract

namespace Subcomplex

variable (A : X.Subcomplex)

structure DeformationRetract extends SSet.DeformationRetract A X where
  i_eq_ι : i = A.ι

structure RelativeDeformationRetract (p : X ⟶ B)
    extends SSet.RelativeDeformationRetract (A.ι ≫ p) p where
  i_eq_ι : i = A.ι

end Subcomplex

end SSet
