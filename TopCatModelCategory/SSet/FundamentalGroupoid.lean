import TopCatModelCategory.SSet.Homotopy

universe u

open CategoryTheory Category Simplicial Limits

namespace SSet

variable {X : SSet.{u}}

lemma yonedaEquiv_symm_zero (x : X _[0]) :
    (yonedaEquiv _ _).symm x = const x := by
  apply (yonedaEquiv _ _).injective
  simp [yonedaEquiv, yonedaCompUliftFunctorEquiv]

namespace subcomplexBoundary₁

def ι₀ : Δ[0] ⟶ (subcomplexBoundary 1 : SSet.{u}) := sorry

def ι₁ : Δ[0] ⟶ (subcomplexBoundary 1 : SSet.{u}) := sorry

def isColimit : IsColimit (BinaryCofan.mk ι₀.{u} ι₁) := sorry

@[ext]
lemma hom_ext {f g : (subcomplexBoundary 1 : SSet) ⟶ X}
    (h₀ : ι₀ ≫ f = ι₀ ≫ g) (h₁ : ι₁ ≫ f = ι₁ ≫ g) : f = g := by
  apply BinaryCofan.IsColimit.hom_ext isColimit <;> assumption

def desc (x₀ x₁ : X _[0]) : (subcomplexBoundary 1 : SSet) ⟶ X :=
  (BinaryCofan.IsColimit.desc' isColimit ((yonedaEquiv _ _).symm x₀)
    ((yonedaEquiv _ _).symm x₁)).1

@[reassoc (attr := simp)]
lemma ι₀_desc (x₀ x₁ : X _[0]) : ι₀ ≫ desc x₀ x₁ = (yonedaEquiv _ _).symm x₀ :=
  (BinaryCofan.IsColimit.desc' isColimit _ _).2.1

@[reassoc (attr := simp)]
lemma ι₁_desc (x₀ x₁ : X _[0]) : ι₁ ≫ desc x₀ x₁ = (yonedaEquiv _ _).symm x₁ :=
  (BinaryCofan.IsColimit.desc' isColimit _ _).2.2

end subcomplexBoundary₁

namespace KanComplex

variable (X)

structure FundamentalGroupoid where
  pt : X _[0]

namespace FundamentalGroupoid

variable {X}

def objEquiv : FundamentalGroupoid X ≃ X _[0] where
  toFun x := x.pt
  invFun x := { pt := x}
  left_inv _ := rfl
  right_inv _ := rfl

def Hom (x₀ x₁ : FundamentalGroupoid X) :=
  Subcomplex.RelativeMorphism.HomotopyClass.{u} _ _
    (subcomplexBoundary₁.desc x₀.pt x₁.pt ≫ (Subcomplex.topIso X).inv)

abbrev Path (x₀ x₁ : FundamentalGroupoid X) :=
  Subcomplex.RelativeMorphism.{u} _ _
    (subcomplexBoundary₁.desc x₀.pt x₁.pt ≫ (Subcomplex.topIso X).inv)

def Path.id (x : FundamentalGroupoid X) : Path x x where
  map := const x.pt
  comm := by
    apply subcomplexBoundary₁.hom_ext
    · rw [assoc, subcomplexBoundary₁.ι₀_desc_assoc, comp_const, comp_const,
        yonedaEquiv_symm_zero, const_comp, FunctorToTypes.comp, Subpresheaf.ι_app,
        Subcomplex.topIso_inv_app_coe]
    · rw [assoc, subcomplexBoundary₁.ι₁_desc_assoc, comp_const, comp_const,
        yonedaEquiv_symm_zero, const_comp, FunctorToTypes.comp, Subpresheaf.ι_app,
        Subcomplex.topIso_inv_app_coe]

namespace Path

variable {x₀ x₁ x₂ : FundamentalGroupoid X}

structure CompStruct (p₀₁ : Path x₀ x₁) (p₁₂ : Path x₁ x₂) (p₀₂ : Path x₀ x₂) where
  map : Δ[2] ⟶ X
  h₀₁ : standardSimplex.map (SimplexCategory.δ 2) ≫ map = p₀₁.map
  h₁₂ : standardSimplex.map (SimplexCategory.δ 0) ≫ map = p₁₂.map
  h₀₂ : standardSimplex.map (SimplexCategory.δ 1) ≫ map = p₀₂.map

lemma exists_compStruct (p₀₁ : Path x₀ x₁) (p₁₂ : Path x₁ x₂) :
    ∃ (p₀₂ : Path x₀ x₂), Nonempty (CompStruct p₀₁ p₁₂ p₀₂) := sorry

def compUniqueUpToHomotopy
    {p₀₁ p₀₁' : Path x₀ x₁} {p₁₂ p₁₂' : Path x₁ x₂} {p₀₂ p₀₂' : Path x₀ x₂}
    (s : CompStruct p₀₁ p₁₂ p₀₂) (s' : CompStruct p₀₁' p₁₂' p₀₂')
    (h₀₁ : p₀₁.Homotopy p₀₁') (h₀₁ : p₁₂.Homotopy p₁₂') :
    p₀₂.Homotopy p₀₂' := sorry

noncomputable def comp (p₀₁ : Path x₀ x₁) (p₁₂ : Path x₁ x₂) :
    Path x₀ x₂ :=
  (exists_compStruct p₀₁ p₁₂).choose

noncomputable def compStruct (p₀₁ : Path x₀ x₁) (p₁₂ : Path x₁ x₂) :
    CompStruct p₀₁ p₁₂ (p₀₁.comp p₁₂) :=
  (exists_compStruct p₀₁ p₁₂).choose_spec.some

end Path

def Hom.id (x : FundamentalGroupoid X) : Hom x x :=
  (Path.id x).homotopyClass

noncomputable def Hom.comp {x₀ x₁ x₂ : FundamentalGroupoid X} (f : Hom x₀ x₁) (g : Hom x₁ x₂) :
    Hom x₀ x₂ := by
  refine Quot.lift₂ (fun p₀₁ p₁₂ ↦ (Path.comp p₀₁ p₁₂).homotopyClass) ?_ ?_ f g
  · sorry
  · sorry

noncomputable instance : CategoryStruct (FundamentalGroupoid X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

def homMk {x₀ x₁ : FundamentalGroupoid X} (p : Path x₀ x₁) :
    x₀ ⟶ x₁ :=
  p.homotopyClass

lemma homMk_eq_of_homotopy {p q : Path x₀ x₁} (h : p.Homotopy q) :
    homMk p = homMk q :=
  h.eq

variable {x₀ x₁ x₂ : FundamentalGroupoid X}

lemma Path.CompStruct.fac {x₀ x₁ x₂ : FundamentalGroupoid X}
    {p₀₁ : Path x₀ x₁} {p₁₂ : Path x₁ x₂} {p₀₂ : Path x₀ x₂}
    (h : CompStruct p₀₁ p₁₂ p₀₂) : homMk p₀₁ ≫ homMk p₁₂ = homMk p₀₂ :=
  homMk_eq_of_homotopy (compUniqueUpToHomotopy (Path.compStruct p₀₁ p₁₂)
    h (.refl _) (.refl _))

end FundamentalGroupoid

end KanComplex

end SSet
