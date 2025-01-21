import TopCatModelCategory.CommSq
import TopCatModelCategory.IsFibrant
import TopCatModelCategory.SSet.Horn
import TopCatModelCategory.SSet.HomotopyBasic
import TopCatModelCategory.SSet.AnodyneExtensions

universe u

open HomotopicalAlgebra CategoryTheory Category Simplicial Limits MonoidalCategory
  ChosenFiniteProducts

namespace SSet

variable {X : SSet.{u}}

lemma yonedaEquiv_symm_zero (x : X _[0]) :
    (yonedaEquiv _ _).symm x = const x := by
  apply (yonedaEquiv _ _).injective
  simp [yonedaEquiv, yonedaCompUliftFunctorEquiv]

namespace standardSimplex

variable (X) {Y : SSet.{u}}

def isTerminalObj₀ : IsTerminal (Δ[0] : SSet.{u}) :=
  IsTerminal.ofUniqueHom (fun _ ↦ SSet.const (obj₀Equiv.symm 0)) (by aesop_cat)

noncomputable def leftUnitor : Δ[0] ⊗ X ≅ X where
  hom := snd _ _
  inv := lift (isTerminalObj₀.from _) (𝟙 X)

@[reassoc (attr := simp)]
lemma leftUnitor_inv_snd : (leftUnitor X).inv ≫ snd _ _ = 𝟙 _ := rfl

variable {X} in
@[reassoc (attr := simp)]
lemma leftUnitor_inv_naturality (f : X ⟶ Y) :
    (leftUnitor X).inv ≫ _ ◁ f = f ≫ (leftUnitor Y).inv := rfl

@[reassoc (attr := simp)]
lemma leftUnitor_inv_map_δ_zero :
    (standardSimplex.leftUnitor X).inv ≫ standardSimplex.map (SimplexCategory.δ 0) ▷ X =
      ι₁ := rfl

@[reassoc (attr := simp)]
lemma leftUnitor_inv_map_δ_one :
    (standardSimplex.leftUnitor X).inv ≫ standardSimplex.map (SimplexCategory.δ 1) ▷ X =
      ι₀ := rfl

noncomputable def rightUnitor : X ⊗ Δ[0] ≅ X where
  hom := fst _ _
  inv := lift (𝟙 X) (isTerminalObj₀.from _)

@[reassoc (attr := simp)]
lemma rightUnitor_inv_map_δ_zero :
    (standardSimplex.rightUnitor X).inv ≫ X ◁ standardSimplex.map (SimplexCategory.δ 0) =
      ι₁ ≫ (β_ _ _).hom := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_inv_map_δ_one :
    (standardSimplex.rightUnitor X).inv ≫ X ◁ standardSimplex.map (SimplexCategory.δ 1) =
      ι₀ ≫ (β_ _ _).hom := rfl

end standardSimplex

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

@[reassoc (attr := simp)]
lemma ι₀_ι : ι₀.{u} ≫ (subcomplexBoundary 1).ι =
    standardSimplex.map (SimplexCategory.δ 1) := by
  apply (yonedaEquiv _ _ ).injective
  ext i
  fin_cases i
  rfl

@[reassoc (attr := simp)]
lemma ι₁_ι : ι₁.{u} ≫ (subcomplexBoundary 1).ι =
    standardSimplex.map (SimplexCategory.δ 0) := by
  apply (yonedaEquiv _ _ ).injective
  ext i
  fin_cases i
  rfl

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

def isColimitRightTensor (X : SSet.{u}): IsColimit (BinaryCofan.mk (ι₀ ▷ X) (ι₁ ▷ X)) :=
  sorry

def isColimitLeftTensor (X : SSet.{u}): IsColimit (BinaryCofan.mk (X ◁ ι₀) (X ◁ ι₁)) :=
  sorry

end subcomplexBoundary₁

namespace KanComplex

variable (X)
structure FundamentalGroupoid [IsFibrant X] where
  pt : X _[0]

variable [IsFibrant X]

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

@[simps]
def Path.mk {x₀ x₁ : FundamentalGroupoid X} (f : Δ[1] ⟶ X)
    (h₀ : standardSimplex.map (SimplexCategory.δ 1) ≫ f = const x₀.pt := by simp)
    (h₁ : standardSimplex.map (SimplexCategory.δ 0) ≫ f = const x₁.pt := by simp) :
    Path x₀ x₁ where
  map := f
  comm := by
    apply subcomplexBoundary₁.hom_ext
    · dsimp
      rw [assoc, subcomplexBoundary₁.ι₀_desc_assoc, yonedaEquiv_symm_zero, const_comp,
        subcomplexBoundary₁.ι₀_ι_assoc, h₀, FunctorToTypes.comp,
        Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe]
    · dsimp
      rw [assoc, subcomplexBoundary₁.ι₁_desc_assoc, yonedaEquiv_symm_zero, const_comp,
        subcomplexBoundary₁.ι₁_ι_assoc, h₁, FunctorToTypes.comp,
        Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe]

@[reassoc]
lemma Path.comm₀ {x₀ x₁ : FundamentalGroupoid X} (p : Path x₀ x₁) :
    standardSimplex.map (SimplexCategory.δ 1) ≫ p.map = const x₀.pt := by
  have := subcomplexBoundary₁.ι₀ ≫= p.comm
  rw [assoc, subcomplexBoundary₁.ι₀_ι_assoc, subcomplexBoundary₁.ι₀_desc_assoc,
    yonedaEquiv_symm_zero, const_comp, FunctorToTypes.comp, Subpresheaf.ι_app,
    Subcomplex.topIso_inv_app_coe] at this
  exact this

@[reassoc]
lemma Path.comm₁ {x₀ x₁ : FundamentalGroupoid X} (p : Path x₀ x₁) :
    standardSimplex.map (SimplexCategory.δ 0) ≫ p.map = const x₁.pt := by
  have := subcomplexBoundary₁.ι₁ ≫= p.comm
  rw [assoc, subcomplexBoundary₁.ι₁_ι_assoc, subcomplexBoundary₁.ι₁_desc_assoc,
    yonedaEquiv_symm_zero, const_comp, FunctorToTypes.comp, Subpresheaf.ι_app,
    Subcomplex.topIso_inv_app_coe] at this
  exact this

def Path.id (x : FundamentalGroupoid X) : Path x x :=
  Path.mk (const x.pt)

namespace Path

section

variable {x₀ x₁ : FundamentalGroupoid X} (p q : Path x₀ x₁)

nonrec abbrev Homotopy := p.Homotopy q

namespace Homotopy

variable {p q} (h : p.Homotopy q)

@[reassoc (attr := simp)]
lemma comm₀ : ι₀ ≫ (β_ _ _).hom ≫ h.h = const x₀.pt := by
  sorry

@[reassoc (attr := simp)]
lemma comm₁ : ι₁ ≫ (β_ _ _).hom ≫ h.h = const x₁.pt := by
  sorry

end Homotopy

end

variable {x₀ x₁ x₂ : FundamentalGroupoid X}

structure CompStruct (p₀₁ : Path x₀ x₁) (p₁₂ : Path x₁ x₂) (p₀₂ : Path x₀ x₂) where
  map : Δ[2] ⟶ X
  h₀₁ : standardSimplex.map (SimplexCategory.δ 2) ≫ map = p₀₁.map
  h₁₂ : standardSimplex.map (SimplexCategory.δ 0) ≫ map = p₁₂.map
  h₀₂ : standardSimplex.map (SimplexCategory.δ 1) ≫ map = p₀₂.map

namespace CompStruct

attribute [reassoc (attr := simp)] h₀₁ h₁₂ h₀₂

end CompStruct

lemma exists_compStruct (p₀₁ : Path x₀ x₁) (p₁₂ : Path x₁ x₂) :
    ∃ (p₀₂ : Path x₀ x₂), Nonempty (CompStruct p₀₁ p₁₂ p₀₂) := by
  obtain ⟨α, h₀₁, h₁₂⟩ := subcomplexHorn₂₁.isPushout.exists_desc p₀₁.map p₁₂.map (by
    have h₀ := subcomplexBoundary₁.ι₁ ≫= p₀₁.comm
    have h₁ := subcomplexBoundary₁.ι₀ ≫= p₁₂.comm
    rw [assoc, subcomplexBoundary₁.ι₁_ι_assoc,
      subcomplexBoundary₁.ι₁_desc_assoc] at h₀
    rw [assoc, subcomplexBoundary₁.ι₀_ι_assoc,
      subcomplexBoundary₁.ι₀_desc_assoc] at h₁
    rw [h₀, h₁])
  obtain ⟨β, hβ⟩ := anodyneExtensions.exists_lift_of_isFibrant α
    (anodyneExtensions.subcomplexHorn_ι_mem 1 1)
  have h₀₁' := subcomplexHorn₂₁.ι₀₁ ≫= hβ
  rw [subcomplexHorn₂₁.ι₀₁_ι_assoc, h₀₁] at h₀₁'
  have h₀₂' := subcomplexHorn₂₁.ι₁₂ ≫= hβ
  rw [subcomplexHorn₂₁.ι₁₂_ι_assoc, h₁₂] at h₀₂'
  refine ⟨Path.mk (standardSimplex.map (SimplexCategory.δ 1) ≫ β) ?_ ?_,
    ⟨{ map := β, h₀₁ := h₀₁', h₁₂ := h₀₂', h₀₂ := rfl }⟩⟩
  · have := SimplexCategory.δ_comp_δ_self (n := 0) (i := 1)
    dsimp at this
    rw [← Functor.map_comp_assoc, this, Functor.map_comp_assoc, h₀₁', p₀₁.comm₀]
  · have := SimplexCategory.δ_comp_δ (n := 0) (i := 0) (j := 0) (by simp)
    dsimp at this
    rw [← Functor.map_comp_assoc, this, Functor.map_comp_assoc, h₀₂', p₁₂.comm₁]

-- consequence of the closed monoidal structure
instance (Y : SSet) : (tensorLeft Y).IsLeftAdjoint := sorry

noncomputable def compUniqueUpToHomotopy
    {p₀₁ p₀₁' : Path x₀ x₁} {p₁₂ p₁₂' : Path x₁ x₂} {p₀₂ p₀₂' : Path x₀ x₂}
    (s : CompStruct p₀₁ p₁₂ p₀₂) (s' : CompStruct p₀₁' p₁₂' p₀₂')
    (h₀₁ : p₀₁.Homotopy p₀₁') (h₁₂ : p₁₂.Homotopy p₁₂') :
    p₀₂.Homotopy p₀₂' := by
  apply Nonempty.some
  obtain ⟨α, hα₁, hα₂⟩ := (subcomplexHorn₂₁.isPushout.{u}.map (tensorLeft Δ[1])).exists_desc
    (h₀₁.h) (h₁₂.h) (by
      dsimp
      rw [← cancel_epi (standardSimplex.rightUnitor Δ[1]).inv,
        standardSimplex.rightUnitor_inv_map_δ_zero_assoc,
        standardSimplex.rightUnitor_inv_map_δ_one_assoc,
        h₀₁.comm₁, h₁₂.comm₀])
  obtain ⟨β, hβ₁, hβ₂⟩ :=
    BinaryCofan.IsColimit.desc' (subcomplexBoundary₁.isColimitRightTensor.{u} Δ[2])
      (snd _ _ ≫ s.map) (snd _ _ ≫ s'.map)
  dsimp at α hα₁ hα₂ β hβ₁ hβ₂
  obtain ⟨γ, hγ₁, hγ₂⟩ := (Subcomplex.unionProd.isPushout _ _).exists_desc α β (by
    apply BinaryCofan.IsColimit.hom_ext (subcomplexBoundary₁.isColimitRightTensor _)
    · dsimp
      rw [← comp_whiskerRight_assoc, subcomplexBoundary₁.ι₀_ι,
        ← cancel_epi (standardSimplex.leftUnitor _).inv]
      apply subcomplexHorn₂₁.isPushout.hom_ext
      · have := (standardSimplex.map (SimplexCategory.δ 1)) ▷ _ ≫= hα₁
        rw [← cancel_epi (standardSimplex.leftUnitor _).inv,
          ← whisker_exchange_assoc,
          standardSimplex.leftUnitor_inv_naturality_assoc,
          standardSimplex.leftUnitor_inv_map_δ_one_assoc,
          standardSimplex.leftUnitor_inv_map_δ_one_assoc, h₀₁.h₀] at this
        rw [standardSimplex.leftUnitor_inv_map_δ_one_assoc, this,
          ← whisker_exchange_assoc, standardSimplex.leftUnitor_inv_naturality_assoc,
          subcomplexHorn₂₁.ι₀₁_ι_assoc, hβ₁, standardSimplex.leftUnitor_inv_snd_assoc,
          CompStruct.h₀₁]
      · have := (standardSimplex.map (SimplexCategory.δ 1)) ▷ _ ≫= hα₂
        rw [← cancel_epi (standardSimplex.leftUnitor _).inv,
          ← whisker_exchange_assoc,
          standardSimplex.leftUnitor_inv_naturality_assoc,
          standardSimplex.leftUnitor_inv_map_δ_one_assoc,
          standardSimplex.leftUnitor_inv_map_δ_one_assoc, h₁₂.h₀] at this
        rw [standardSimplex.leftUnitor_inv_map_δ_one_assoc, this,
          ← whisker_exchange_assoc, standardSimplex.leftUnitor_inv_naturality_assoc,
          subcomplexHorn₂₁.ι₁₂_ι_assoc, hβ₁, standardSimplex.leftUnitor_inv_snd_assoc,
          CompStruct.h₁₂]
    · dsimp
      rw [← comp_whiskerRight_assoc, subcomplexBoundary₁.ι₁_ι,
        ← cancel_epi (standardSimplex.leftUnitor _).inv]
      apply subcomplexHorn₂₁.isPushout.hom_ext
      · have := (standardSimplex.map (SimplexCategory.δ 0)) ▷ _ ≫= hα₁
        rw [← cancel_epi (standardSimplex.leftUnitor _).inv,
          ← whisker_exchange_assoc,
          standardSimplex.leftUnitor_inv_naturality_assoc,
          standardSimplex.leftUnitor_inv_map_δ_zero_assoc,
          standardSimplex.leftUnitor_inv_map_δ_zero_assoc, h₀₁.h₁] at this
        rw [standardSimplex.leftUnitor_inv_map_δ_zero_assoc, this,
          ← whisker_exchange_assoc, standardSimplex.leftUnitor_inv_naturality_assoc,
          subcomplexHorn₂₁.ι₀₁_ι_assoc, hβ₂, standardSimplex.leftUnitor_inv_snd_assoc,
          CompStruct.h₀₁]
      · have := (standardSimplex.map (SimplexCategory.δ 0)) ▷ _ ≫= hα₂
        rw [← cancel_epi (standardSimplex.leftUnitor _).inv,
          ← whisker_exchange_assoc,
          standardSimplex.leftUnitor_inv_naturality_assoc,
          standardSimplex.leftUnitor_inv_map_δ_zero_assoc,
          standardSimplex.leftUnitor_inv_map_δ_zero_assoc, h₁₂.h₁] at this
        rw [standardSimplex.leftUnitor_inv_map_δ_zero_assoc, this,
          ← whisker_exchange_assoc, standardSimplex.leftUnitor_inv_naturality_assoc,
          subcomplexHorn₂₁.ι₁₂_ι_assoc, hβ₂, standardSimplex.leftUnitor_inv_snd_assoc,
          CompStruct.h₁₂])
  obtain ⟨h, fac⟩ := anodyneExtensions.exists_lift_of_isFibrant γ
    (anodyneExtensions.subcomplex_unionProd_mem_of_right.{u} (subcomplexBoundary 1)
    (subcomplexHorn 2 1) (anodyneExtensions.subcomplexHorn_ι_mem 1 1))
  exact ⟨{
    h := _ ◁ standardSimplex.map (SimplexCategory.δ 1) ≫ h
    h₀ := by
      have := (standardSimplex.leftUnitor _).inv ≫= hβ₁
      rw [standardSimplex.leftUnitor_inv_snd_assoc] at this
      rw [← s.h₀₂, ← this, ← hγ₂, ← fac]
      rfl
    h₁ := by
      have := (standardSimplex.leftUnitor _).inv ≫= hβ₂
      rw [standardSimplex.leftUnitor_inv_snd_assoc] at this
      rw [← s'.h₀₂, ← this, ← hγ₂, ← fac]
      rfl
    rel := by
      apply BinaryCofan.IsColimit.hom_ext (subcomplexBoundary₁.isColimitLeftTensor _)
      · have h₀ := (Δ[1] ◁ subcomplexBoundary₁.ι₀ ≫ Δ[1] ◁ Subpresheaf.ι (subcomplexBoundary 1) ≫
          Δ[1] ◁ subcomplexHorn₂₁.ι₀₁ ≫ Subcomplex.unionProd.ι₁ _ _) ≫= fac
        rw [assoc, assoc, assoc, assoc, assoc, assoc, Subcomplex.unionProd.ι₁_ι_assoc,
          hγ₁, hα₁, h₀₁.rel, assoc, whiskerLeft_snd_assoc,
          subcomplexBoundary₁.ι₀_desc_assoc, yonedaEquiv_symm_zero, const_comp, comp_const,
          FunctorToTypes.comp, Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe] at h₀
        dsimp
        rw [assoc, whiskerLeft_snd_assoc, subcomplexBoundary₁.ι₀_desc_assoc,
          yonedaEquiv_symm_zero, const_comp, comp_const,
          FunctorToTypes.comp, Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe,
          ← MonoidalCategory.whiskerLeft_comp_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc,
          subcomplexBoundary₁.ι₀_ι, ← h₀,
          ← MonoidalCategory.whiskerLeft_comp_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, assoc, assoc,
          subcomplexHorn₂₁.ι₀₁_ι, subcomplexBoundary₁.ι₀_ι_assoc,
          ← Functor.map_comp, ← Functor.map_comp]
        congr 3
        apply SimplexCategory.δ_comp_δ_self
      · have h₂ := (Δ[1] ◁ subcomplexBoundary₁.ι₁ ≫ Δ[1] ◁ Subpresheaf.ι (subcomplexBoundary 1) ≫
          Δ[1] ◁ subcomplexHorn₂₁.ι₁₂ ≫ Subcomplex.unionProd.ι₁ _ _) ≫= fac
        rw [assoc, assoc, assoc, assoc, assoc, assoc, Subcomplex.unionProd.ι₁_ι_assoc,
          hγ₁, hα₂, h₁₂.rel, assoc, whiskerLeft_snd_assoc,
          subcomplexBoundary₁.ι₁_desc_assoc, yonedaEquiv_symm_zero, const_comp, comp_const,
          FunctorToTypes.comp, Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe] at h₂
        dsimp
        rw [assoc, whiskerLeft_snd_assoc, subcomplexBoundary₁.ι₁_desc_assoc,
          yonedaEquiv_symm_zero, const_comp, comp_const,
          FunctorToTypes.comp, Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe,
          ← MonoidalCategory.whiskerLeft_comp_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc,
          subcomplexBoundary₁.ι₁_ι, ← h₂,
          ← MonoidalCategory.whiskerLeft_comp_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, assoc, assoc,
          subcomplexHorn₂₁.ι₁₂_ι, subcomplexBoundary₁.ι₁_ι_assoc,
          ← Functor.map_comp, ← Functor.map_comp]
        congr 3 }⟩

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

lemma homMk_eq_of_homotopy {x₀ x₁ : FundamentalGroupoid X}
    {p q : Path x₀ x₁} (h : p.Homotopy q) :
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
