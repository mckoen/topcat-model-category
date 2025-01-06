import TopCatModelCategory.IsFibrant
import TopCatModelCategory.SSet.AnodyneExtensions

open HomotopicalAlgebra CategoryTheory Simplicial MonoidalCategory Opposite
  ChosenFiniteProducts

universe u

namespace SSet

@[simps]
def const {X Y : SSet.{u}} (y : Y _[0]) : X ⟶ Y where
  app n _ := Y.map (n.unop.const _ 0).op y
  naturality n m f := by
    ext
    dsimp
    rw [← FunctorToTypes.map_comp_apply]
    rfl

private noncomputable abbrev ι₀ {X : SSet.{u}} : X ⟶ Δ[1] ⊗ X :=
  lift (const (standardSimplex.obj₀Equiv.{u}.symm 0)) (𝟙 X)

private noncomputable abbrev ι₁ {X : SSet.{u}} : X ⟶ Δ[1] ⊗ X :=
  lift (const (standardSimplex.obj₀Equiv.{u}.symm 1)) (𝟙 X)

namespace Subcomplex

variable {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) (φ : (A : SSet) ⟶ (B : SSet))

structure RelativeMorphism where
  map : X ⟶ Y
  comm : A.ι ≫ map = φ ≫ B.ι

namespace RelativeMorphism

attribute [reassoc (attr := simp)] comm

variable {A B φ} (f g : RelativeMorphism A B φ)

lemma map_eq_of_mem {n : SimplexCategoryᵒᵖ} (a : X.obj n) (ha : a ∈ A.obj n) :
    f.map.app n a = φ.app n ⟨a, ha⟩ :=
  congr_fun (congr_app f.comm n) ⟨a, ha⟩

@[simp]
lemma map_coe {n : SimplexCategoryᵒᵖ} (a : A.obj n) :
    f.map.app n a = φ.app n a := by
  apply map_eq_of_mem

lemma image_le : A.image f.map ≤ B := by
  rintro n _ ⟨a, ha, rfl⟩
  have := f.map_coe ⟨a, ha⟩
  aesop

lemma le_preimage : A ≤ B.preimage f.map := by
  simpa only [← image_le_iff] using f.image_le

structure Homotopy where
  h : Δ[1] ⊗ X ⟶ Y
  h₀ : ι₀ ≫ h = f.map := by aesop_cat
  h₁ : ι₁ ≫ h = g.map := by aesop_cat
  rel : _ ◁ A.ι ≫ h = snd _ _ ≫ φ ≫ B.ι := by aesop_cat

namespace Homotopy

@[simps]
noncomputable def refl : Homotopy f f where
  h := snd _ _ ≫ f.map

end Homotopy

variable (A B φ)

def HomotopyClass : Type u :=
  Quot (α := RelativeMorphism A B φ) (fun f g ↦ Nonempty (Homotopy f g))

end RelativeMorphism

end Subcomplex

section

variable (X : SSet.{u})

def π₀ := Quot (α := X _[0]) (fun x y ↦ ∃ (p : X _[1]), X.δ 1 p = x ∧ X.δ 0 p = y)

def toπ₀ (x : X _[0]) : π₀ X := Quot.mk _ x

lemma toπ₀_surjective : Function.Surjective X.toπ₀ := by
  apply Quot.mk_surjective

lemma toπ₀_congr (p : X _[1]) : X.toπ₀ (X.δ 1 p) = X.toπ₀ (X.δ 0 p) :=
  Quot.sound ⟨p, rfl, rfl⟩

end

namespace KanComplex

variable (X : SSet.{u}) (n : ℕ) (x : X _[0])

def π : Type u :=
  Subcomplex.RelativeMorphism.HomotopyClass
    (subcomplexBoundary n) (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

end KanComplex

end SSet
