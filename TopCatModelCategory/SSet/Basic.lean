import Mathlib.AlgebraicTopology.SimplicialSet.Basic

universe u

open CategoryTheory Simplicial Opposite

namespace SSet

@[simps]
def const {X Y : SSet.{u}} (y : Y _[0]) : X ⟶ Y where
  app n _ := Y.map (n.unop.const _ 0).op y
  naturality n m f := by
    ext
    dsimp
    rw [← FunctorToTypes.map_comp_apply]
    rfl

@[reassoc (attr := simp)]
lemma comp_const {X Y Z : SSet.{u}} (f : X ⟶ Y) (z : Z _[0]) :
    f ≫ const z = const z := rfl

@[reassoc (attr := simp)]
lemma const_comp {X Y Z : SSet.{u}} (y : Y _[0]) (g : Y ⟶ Z) :
    const (X := X) y ≫ g = const (g.app _ y) := by
  ext m x
  simp [FunctorToTypes.naturality]

lemma yonedaEquiv_apply_comp {X Y : SSet.{u}} {n : SimplexCategory}
    (f : standardSimplex.obj n ⟶ X) (g : X ⟶ Y) :
    yonedaEquiv _ _ (f ≫ g) = g.app _ (yonedaEquiv _ _ f) := rfl

@[reassoc]
lemma standardSimplex.map_comp_yonedaEquiv_symm {X : SSet.{u}} {n m : SimplexCategory}
    (x : X.obj (op n)) (f : m ⟶ n) :
      standardSimplex.map f ≫ (yonedaEquiv _ _).symm x =
        (yonedaEquiv _ _).symm (X.map f.op x) := by
  apply (yonedaEquiv _ _).injective
  conv_rhs => rw [Equiv.apply_symm_apply, ← Category.id_comp f]
  rfl

lemma yonedaEquiv_const {X : SSet.{u}} (x : X _[0]) :
    (yonedaEquiv _ _) (const x : Δ[0] ⟶ X) = x := by
  simp [yonedaEquiv, yonedaCompUliftFunctorEquiv]

@[simp]
lemma yonedaEquiv_symm_zero {X : SSet.{u}} (x : X _[0]) :
    (yonedaEquiv _ _).symm x = const x := by
  apply (yonedaEquiv _ _).injective
  simp [yonedaEquiv_const]

end SSet
