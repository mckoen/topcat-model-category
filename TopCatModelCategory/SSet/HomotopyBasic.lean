import TopCatModelCategory.SSet.Basic
import TopCatModelCategory.SSet.Fiber
import TopCatModelCategory.SSet.StandardSimplex
import TopCatModelCategory.SSet.Subcomplex

open CategoryTheory Category Simplicial MonoidalCategory Opposite
  ChosenFiniteProducts Limits

universe u

namespace SSet

noncomputable abbrev ι₀ {X : SSet.{u}} : X ⟶ Δ[1] ⊗ X :=
  lift (const (standardSimplex.obj₀Equiv.{u}.symm 0)) (𝟙 X)

@[reassoc (attr := simp)]
lemma ι₀_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₀ ≫ _ ◁ f = f ≫ ι₀ := rfl

noncomputable abbrev ι₁ {X : SSet.{u}} : X ⟶ Δ[1] ⊗ X :=
  lift (const (standardSimplex.obj₀Equiv.{u}.symm 1)) (𝟙 X)

@[reassoc (attr := simp)]
lemma ι₁_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₁ ≫ _ ◁ f = f ≫ ι₁ := rfl

namespace Subcomplex

variable {X Y Z : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
  (φ : (A : SSet) ⟶ (B : SSet))

structure RelativeMorphism where
  map : X ⟶ Y
  comm : A.ι ≫ map = φ ≫ B.ι := by aesop_cat

namespace RelativeMorphism

attribute [reassoc (attr := simp)] comm

@[simps]
def ofSimplex₀ (f : X ⟶ Y) (x : X _[0]) (y : Y _[0])
    (h : f.app _ x = y) :
    RelativeMorphism (.ofSimplex x) (.ofSimplex y)
      (SSet.const ⟨y, mem_ofSimplex_obj y⟩) where
  map := f
  comm := by
    rw [ofSimplex_ι, ofSimplex_ι, const_comp, comp_const, h]

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

attribute [reassoc (attr := simp)] h₀ h₁ rel

@[simps]
noncomputable def refl : Homotopy f f where
  h := snd _ _ ≫ f.map

end Homotopy

variable (A B φ)

def HomotopyClass : Type u :=
  Quot (α := RelativeMorphism A B φ) (fun f g ↦ Nonempty (Homotopy f g))

variable {A B φ}

def homotopyClass (f : RelativeMorphism A B φ) : HomotopyClass A B φ := Quot.mk _ f

lemma Homotopy.eq {f g : RelativeMorphism A B φ} (h : Homotopy f g) :
    f.homotopyClass = g.homotopyClass :=
  Quot.sound ⟨h⟩

lemma HomotopyClass.eq_homotopyClass (x : HomotopyClass A B φ) :
    ∃ (f : RelativeMorphism A B φ), f.homotopyClass = x :=
  Quot.mk_surjective x

variable {C : Z.Subcomplex} {ψ : (B : SSet) ⟶ (C : SSet)}

@[simps]
def comp (f' : RelativeMorphism B C ψ) {φψ : (A : SSet) ⟶ (C : SSet)}
    (fac : φ ≫ ψ = φψ) : RelativeMorphism A C φψ where
  map := f.map ≫ f'.map

variable {f g}

@[simps]
noncomputable def Homotopy.postcomp (h : Homotopy f g)
    (f' : RelativeMorphism B C ψ) {φψ : (A : SSet) ⟶ (C : SSet)}
    (fac : φ ≫ ψ = φψ) :
    Homotopy (f.comp f' fac) (g.comp f' fac) where
  h := h.h ≫ f'.map
  rel := by simp [h.rel_assoc, ← fac]

noncomputable def Homotopy.precomp
    {f' g' : RelativeMorphism B C ψ} (h : Homotopy f' g')
    (f : RelativeMorphism A B φ) {φψ : (A : SSet) ⟶ (C : SSet)}
    (fac : φ ≫ ψ = φψ) :
    Homotopy (f.comp f' fac) (f.comp g' fac) where
  h := _ ◁ f.map ≫ h.h
  rel := by
    rw [← fac, assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      f.comm, MonoidalCategory.whiskerLeft_comp_assoc,
      h.rel, whiskerLeft_snd_assoc]

def HomotopyClass.postcomp (h : HomotopyClass A B φ)
    (f' : RelativeMorphism B C ψ) {φψ : (A : SSet) ⟶ (C : SSet)}
    (fac : φ ≫ ψ = φψ) :
    HomotopyClass A C φψ :=
  Quot.lift (fun f ↦ (f.comp f' fac).homotopyClass)
    (fun _ _ ⟨h⟩ ↦ (h.postcomp f' fac).eq) h

@[simp]
lemma homotopyClass_postcomp
    (f : RelativeMorphism A B φ)
    (f' : RelativeMorphism B C ψ) {φψ : (A : SSet) ⟶ (C : SSet)}
    (fac : φ ≫ ψ = φψ) :
    f.homotopyClass.postcomp f' fac =
      (f.comp f' fac).homotopyClass := rfl

end RelativeMorphism

end Subcomplex

/-section

variable (X : SSet.{u})

def π₀ := Quot (α := X _[0]) (fun x y ↦ ∃ (p : X _[1]), X.δ 1 p = x ∧ X.δ 0 p = y)

def toπ₀ (x : X _[0]) : π₀ X := Quot.mk _ x

lemma toπ₀_surjective : Function.Surjective X.toπ₀ := by
  apply Quot.mk_surjective

lemma toπ₀_congr (p : X _[1]) : X.toπ₀ (X.δ 1 p) = X.toπ₀ (X.δ 0 p) :=
  Quot.sound ⟨p, rfl, rfl⟩

end-/

namespace KanComplex

def π (n : ℕ) (X : SSet.{u}) (x : X _[0]) : Type u :=
  Subcomplex.RelativeMorphism.HomotopyClass
    (subcomplexBoundary n) (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

variable {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
  (x : X _[0]) (y : Y _[0]) (h : f.app _ x = y)

def mapπ (p : π n X x) : π n Y y :=
  p.postcomp (.ofSimplex₀ f x y h) (by rw [comp_const])

end KanComplex

end SSet
