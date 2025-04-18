import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.UnitInterval
import Mathlib.CategoryTheory.ChosenFiniteProducts

universe u

open CategoryTheory Limits MonoidalCategory

namespace TopCat

instance : ChosenFiniteProducts TopCat.{u} where
  terminal := ⟨_, isTerminalPUnit⟩
  product X Y := ⟨prodBinaryFan X Y, X.prodBinaryFanIsLimit Y⟩

@[simp]
theorem tensor_apply {W X Y Z : TopCat.{u}} (f : W ⟶ X) (g : Y ⟶ Z) (p : ↑(W ⊗ Y)) :
    (f ⊗ g).hom p = (f p.1, g p.2) :=
  rfl

@[simp]
theorem whiskerLeft_apply (X : TopCat.{u}) {Y Z : TopCat.{u}} (f : Y ⟶ Z) (p : ↑(X ⊗ Y)) :
    (X ◁ f) p = (p.1, f p.2) :=
  rfl

@[simp]
theorem whiskerRight_apply {Y Z : TopCat.{u}} (f : Y ⟶ Z) (X : TopCat.{u}) (p : ↑(Y ⊗ X)) :
    (f ▷ X) p = (f p.1, p.2) :=
  rfl

@[simp]
theorem leftUnitor_hom_apply {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}} :
    (λ_ X).hom (p, x) = x :=
  rfl

@[simp]
theorem leftUnitor_inv_apply {X : TopCat.{u}} {x : X} :
    (λ_ X).inv x = (PUnit.unit, x) :=
  rfl

@[simp]
theorem rightUnitor_hom_apply {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}} :
    (ρ_ X).hom (x, p) = x :=
  rfl

@[simp]
theorem rightUnitor_inv_apply {X : TopCat.{u}} {x : X} :
    (ρ_ X).inv x = (x, .unit) :=
  rfl

@[simp]
theorem associator_hom_apply {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z} :
    (α_ X Y Z).hom ((x, y), z) = (x, (y, z)) :=
  rfl

@[simp]
theorem associator_inv_apply {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z} :
    (α_ X Y Z).inv (x, (y, z)) = ((x, y), z) :=
  rfl

@[simp] theorem associator_hom_apply_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).1 = x.1.1 :=
  rfl

@[simp] theorem associator_hom_apply_2_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).2.1 = x.1.2 :=
  rfl

@[simp] theorem associator_hom_apply_2_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).2.2 = x.2 :=
  rfl

@[simp] theorem associator_inv_apply_1_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).1.1 = x.1 :=
  rfl

@[simp] theorem associator_inv_apply_1_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).1.2 = x.2.1 :=
  rfl

@[simp] theorem associator_inv_apply_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).2 = x.2.2 :=
  rfl

@[simp]
theorem braiding_hom_apply {X Y : TopCat.{u}} {x : X} {y : Y} :
    (β_ X Y).hom (x, y) = (y, x) :=
  rfl

@[simp]
theorem braiding_inv_apply {X Y : TopCat.{u}} {x : X} {y : Y} :
    (β_ X Y).inv (y, x) = (x, y) :=
  rfl

@[simp]
protected theorem lift_apply {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : X ⟶ Z} {x : X} :
    ChosenFiniteProducts.lift f g x = (f x, g x) :=
  rfl

def I := TopCat.of unitInterval

open ChosenFiniteProducts

noncomputable def ι₀ {X : TopCat.{0}} : X ⟶ X ⊗ I :=
  lift (𝟙 X) (ofHom ⟨_, continuous_const (y := ⟨0, by simp⟩)⟩)

@[reassoc (attr := simp)]
lemma ι₀_comp {X Y : TopCat.{0}} (f : X ⟶ Y) :
    ι₀ ≫ f ▷ _ = f ≫ ι₀ := rfl

@[reassoc (attr := simp)]
lemma ι₀_fst (X : TopCat.{0}) : ι₀ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma ι₀_snd (X : TopCat.{0}) :
    ι₀ ≫ snd X _ = ofHom ⟨_, continuous_const (y := ⟨0, by simp⟩)⟩ :=
  rfl

@[simp]
lemma ι₀_apply {X : TopCat.{0}} (x : X) : ι₀ x = ⟨x, ⟨0, by simp⟩⟩ := rfl

noncomputable def ι₁ {X : TopCat.{0}} : X ⟶ X ⊗ I :=
  lift (𝟙 X) (ofHom ⟨_, continuous_const (y := ⟨1, by simp⟩)⟩)

@[reassoc (attr := simp)]
lemma ι₁_comp {X Y : TopCat.{0}} (f : X ⟶ Y) :
    ι₁ ≫ f ▷ _ = f ≫ ι₁ := rfl

@[reassoc (attr := simp)]
lemma ι₁_fst (X : TopCat.{0}) : ι₀ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma ι₁_snd (X : TopCat.{0}) :
    ι₁ ≫ snd X _ = ofHom ⟨_, continuous_const (y := ⟨1, by simp⟩)⟩ :=
  rfl

@[simp]
lemma ι₁_apply {X : TopCat.{0}} (x : X) : ι₁ x = ⟨x, ⟨1, by simp⟩⟩ :=
  rfl

end TopCat
