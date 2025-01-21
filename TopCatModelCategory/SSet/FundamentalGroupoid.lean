import TopCatModelCategory.CommSq
import TopCatModelCategory.SSet.Boundary
import TopCatModelCategory.SSet.HomotopyBasic

universe u

open CategoryTheory Category Simplicial Limits

namespace SSet

variable {X : SSet.{u}}

lemma yonedaEquiv_symm_zero (x : X _[0]) :
    (yonedaEquiv _ _).symm x = const x := by
  apply (yonedaEquiv _ _).injective
  simp [yonedaEquiv, yonedaCompUliftFunctorEquiv]

namespace subcomplexBoundary₁

lemma sq : Subcomplex.Sq ⊥ (standardSimplex.face {0}) (standardSimplex.face {1})
    (subcomplexBoundary.{u} 1) where
  max_eq := by
    rw [subcomplexBoundary_eq_iSup]
    ext
    rw [Subpresheaf.max_obj, Set.mem_union, Subpresheaf.iSup_obj,
      Set.iSup_eq_iUnion, Set.mem_iUnion]
    constructor
    · rintro (h₀ | h₁)
      · exact ⟨1, h₀⟩
      · exact ⟨0, h₁⟩
    · rintro ⟨i, h⟩
      fin_cases i
      · exact Or.inr h
      · exact Or.inl h
  min_eq := by
    ext ⟨m⟩ x
    induction' m using SimplexCategory.rec with m
    aesop

def ι₀ : Δ[0] ⟶ (subcomplexBoundary 1 : SSet.{u}) :=
  (standardSimplex.isoOfRepresentableBy
    (standardSimplex.faceRepresentableBy.{u} ({1}ᶜ : Finset (Fin 2)) 0
    (Fin.orderIsoSingleton 0))).hom ≫
    Subcomplex.homOfLE (face_le_subcomplexBoundary (1 : Fin 2))

def ι₁ : Δ[0] ⟶ (subcomplexBoundary 1 : SSet.{u}) :=
  (standardSimplex.isoOfRepresentableBy
    (standardSimplex.faceRepresentableBy.{u} ({0}ᶜ : Finset (Fin 2)) 0
    (Fin.orderIsoSingleton 1))).hom ≫
    Subcomplex.homOfLE (face_le_subcomplexBoundary (0 : Fin 2))

lemma isPushout : IsPushout (initial.to _) (initial.to _) ι₀.{u} ι₁.{u} :=
  sq.{u}.isPushout.of_iso' (initialIsoIsInitial Subcomplex.isInitialBot)
    (standardSimplex.isoOfRepresentableBy
      (standardSimplex.faceRepresentableBy.{u} ({1}ᶜ : Finset (Fin 2)) 0
      (Fin.orderIsoSingleton 0)))
    (standardSimplex.isoOfRepresentableBy
      (standardSimplex.faceRepresentableBy.{u} ({0}ᶜ : Finset (Fin 2)) 0
      (Fin.orderIsoSingleton 1))) (Iso.refl _)
    (initialIsInitial.hom_ext _ _) (initialIsInitial.hom_ext _ _)
    (by simp [ι₀]) (by simp [ι₁])

noncomputable def isColimit : IsColimit (BinaryCofan.mk ι₀.{u} ι₁) :=
  isPushout.{u}.isColimitBinaryCofan initialIsInitial

@[ext]
lemma hom_ext {f g : (subcomplexBoundary 1 : SSet) ⟶ X}
    (h₀ : ι₀ ≫ f = ι₀ ≫ g) (h₁ : ι₁ ≫ f = ι₁ ≫ g) : f = g := by
  apply BinaryCofan.IsColimit.hom_ext isColimit <;> assumption

noncomputable def desc (x₀ x₁ : X _[0]) : (subcomplexBoundary 1 : SSet) ⟶ X :=
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
    ∃ (p₀₂ : Path x₀ x₂), Nonempty (CompStruct p₀₁ p₁₂ p₀₂) := by
  sorry

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
  · rintro p₀₁ p₁₂ p₁₂' ⟨h⟩
    exact (Path.compUniqueUpToHomotopy (p₀₁.compStruct p₁₂)
      (p₀₁.compStruct p₁₂') (.refl _) h).eq
  · rintro p₀₁ p₀₁' p₁₂ ⟨h⟩
    exact (Path.compUniqueUpToHomotopy (p₀₁.compStruct p₁₂)
      (p₀₁'.compStruct p₁₂) h (.refl _)).eq

noncomputable instance : CategoryStruct (FundamentalGroupoid X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

def homMk {x₀ x₁ : FundamentalGroupoid X} (p : Path x₀ x₁) :
    x₀ ⟶ x₁ :=
  p.homotopyClass

@[simp]
lemma homMk_refl (x : FundamentalGroupoid X) :
    homMk (Path.id x) = 𝟙 x := rfl

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
