import TopCatModelCategory.SSet.AnodyneExtensions
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

universe u

open CategoryTheory MonoidalCategory Limits Simplicial HomotopicalAlgebra
  ChosenFiniteProducts

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}} {A B : X.Subcomplex} (h : A = B)

@[reassoc (attr := simp)]
lemma isoOfEq_hom_ι : (isoOfEq h).hom ≫ B.ι = A.ι := rfl

@[reassoc (attr := simp)]
lemma isoOfEq_inv_ι : (isoOfEq h).inv ≫ A.ι = B.ι := rfl

end Subcomplex

namespace stdSimplex

lemma face_singleton_eq_const {n : ℕ} (i : Fin (n + 1)) :
    (face.{u} {i}).ι = SSet.const (stdSimplex.obj₀Equiv.symm i) := by
  ext ⟨d⟩ ⟨x, hx⟩ j
  induction' d using SimplexCategory.rec with d
  aesop

end stdSimplex

namespace horn₁₁

lemma eq_face : horn.{u} 1 1 = stdSimplex.face {1} := by
  rw [horn_eq_iSup]
  letI : Unique ({1}ᶜ : Set (Fin 2)) :=
    { default := ⟨0, by simp⟩
      uniq := by rintro ⟨a, _⟩; fin_cases a <;> aesop }
  rw [iSup_unique]
  rfl

lemma ι_eq : (horn.{u} 1 1).ι = const.{u} (stdSimplex.obj₀Equiv.{u}.symm 1) := by
  rw [← Subcomplex.isoOfEq_hom_ι eq_face, stdSimplex.face_singleton_eq_const, comp_const]

noncomputable def iso : Δ[0] ≅ (horn 1 1 : SSet.{u}) :=
  stdSimplex.faceSingletonIso _ ≪≫ Subcomplex.isoOfEq eq_face.symm

@[reassoc (attr := simp)]
lemma iso_hom_ι : iso.{u}.hom ≫ Λ[1, 1].ι = stdSimplex.δ 0 := by
  rw [ι_eq, comp_const]
  apply yonedaEquiv.injective
  ext j
  fin_cases j
  rfl

end horn₁₁

def hornOneUnionProdInclusions : MorphismProperty SSet.{u} :=
  ⨆ (i : Fin 2) (X : SSet.{u}),
    .ofHoms (fun (A : X.Subcomplex) ↦ (A.unionProd (horn.{u} 1 i)).ι)

lemma mem_hornOneUnionProdInclusions (i : Fin 2) {X : SSet.{u}} (A : X.Subcomplex) :
    hornOneUnionProdInclusions (A.unionProd (horn.{u} 1 i)).ι := by
  simp only [hornOneUnionProdInclusions, MorphismProperty.iSup_iff]
  exact ⟨i, X, ⟨A⟩⟩

lemma hornOneUnionProdInclusions_rlp :
    hornOneUnionProdInclusions.{u}.rlp = fibrations SSet := by
  sorry

section

variable {A₁ A₂ B₁ B₂ : SSet.{u}} (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂)

abbrev PushoutTensor := Functor.PushoutObjObj (curriedTensor SSet.{u}) f₁ f₂

namespace PushoutTensor

section

variable {f₁ f₂} (h : PushoutTensor f₁ f₂)

@[simps]
noncomputable def flip : PushoutTensor f₂ f₁ where
  pt := h.pt
  inl := (β_ _ _).hom ≫ h.inr
  inr := (β_ _ _).hom ≫ h.inl
  isPushout := h.isPushout.flip.of_iso (β_ _ _) (β_ _ _) (β_ _ _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma inl_ι_flip : h.inl ≫ h.flip.ι = (β_ _ _).hom ≫ f₂ ▷ _ := by
  rw [← cancel_epi (β_ _ _).hom]
  simpa using h.flip.inr_ι

@[reassoc (attr := simp)]
lemma inr_ι_flip : h.inr ≫ h.flip.ι = (β_ _ _).hom ≫ _ ◁ f₁ := by
  rw [← cancel_epi (β_ _ _).hom]
  simpa using h.flip.inl_ι

@[reassoc]
lemma ι_flip : h.flip.ι = h.ι ≫ (β_ _ _).hom := by
  apply h.isPushout.hom_ext <;> simp

end

section

variable {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)

@[simps]
noncomputable def unionProd : PushoutTensor A.ι B.ι where
  pt := A.unionProd B
  inl := Subcomplex.unionProd.ι₁ A B
  inr := Subcomplex.unionProd.ι₂ A B
  isPushout := Subcomplex.unionProd.isPushout _ _

@[simp]
lemma ι_unionProd : (unionProd A B).ι = (A.unionProd B).ι := by
  apply (unionProd A B).isPushout.hom_ext
  · rw [Functor.PushoutObjObj.inl_ι]
    dsimp
  · rw [Functor.PushoutObjObj.inr_ι]
    dsimp

end

section

variable {X Y : SSet.{u}} (i : X ⟶ Y)

@[simps]
noncomputable def horn₁₀ :
    PushoutTensor i (horn.{u} 1 1).ι where
  pt := pushout i ι₁
  inl := fst _ _ ≫ pushout.inl _ _
  inr := pushout.inr _ _
  isPushout := (IsPushout.of_hasPushout i ι₁).of_iso
      ((stdSimplex.rightUnitor _).symm ≪≫ (Iso.refl _ ⊗ horn₁₁.iso))
      ((stdSimplex.rightUnitor _).symm ≪≫ (Iso.refl _ ⊗ horn₁₁.iso))
      (Iso.refl _) (Iso.refl _) (by aesop_cat) (by
        dsimp
        rw [Category.comp_id, id_tensorHom, Category.assoc,
          ← MonoidalCategory.whiskerLeft_comp, horn₁₁.iso_hom_ι]
        rfl) (by simp) (by simp)

lemma ι_horn₁₀ : (horn₁₀ i).ι = pushout.desc ι₁ (i ▷ Δ[1]) (by simp) := by
  apply (horn₁₀ i).isPushout.hom_ext
  · rw [Functor.PushoutObjObj.inl_ι]
    dsimp
    rw [Category.assoc, pushout.inl_desc, horn₁₁.ι_eq]
    rfl
  · rw [Functor.PushoutObjObj.inr_ι]
    dsimp
    rw [pushout.inr_desc]

end

end PushoutTensor

variable {X Y : SSet.{u}} (f₃ : X ⟶ Y)

abbrev PullbackIhom := Functor.PullbackObjObj MonoidalClosed.internalHom f₁ f₃

end

namespace fibrations

variable {A B S T : SSet.{u}} {i : A ⟶ B} {p : S ⟶ T} (h : PullbackIhom i p)

lemma hasLiftingProperty_unionProd_horn₁_ι_pullbackIhomπ [Mono i] [Fibration p]
    {Y : SSet.{u}} (X : Y.Subcomplex) (k : Fin 2) :
    HasLiftingProperty (X.unionProd Λ[1, k]).ι h.π := by
  sorry

instance [Mono i] [Fibration p] : Fibration h.π := by
  rw [fibration_iff, ← hornOneUnionProdInclusions_rlp]
  intro _ _ _ hj
  simp only [hornOneUnionProdInclusions, MorphismProperty.iSup_iff] at hj
  obtain ⟨_, _, ⟨_⟩⟩ := hj
  apply hasLiftingProperty_unionProd_horn₁_ι_pullbackIhomπ

end fibrations


lemma hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom
    {A₁ A₂ B₁ B₂ : SSet.{u}} {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂} (h₁₂ : PushoutTensor f₁ f₂)
    {X Y : SSet.{u}} {f₃ : X ⟶ Y} (h₁₃ : PullbackIhom f₁ f₃) :
    HasLiftingProperty h₁₂.ι f₃ ↔ HasLiftingProperty f₂ h₁₃.π :=
  MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff h₁₂ h₁₃

namespace anodyneExtensions

section

variable {A₁ A₂ B₁ B₂ : SSet.{u}} {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂}

variable (h₁₂ : PushoutTensor f₁ f₂)

lemma pushoutTensorι₂ [Mono f₁] (hf₂ : anodyneExtensions f₂) : anodyneExtensions h₁₂.ι := by
  dsimp [anodyneExtensions]
  intro X Y p hp
  rw [← fibration_iff] at hp
  let h₁₃ : PullbackIhom f₁ p := Functor.PullbackObjObj.ofHasPullback _ _ _
  rw [hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom _ h₁₃]
  apply hf₂.hasLeftLiftingProperty

lemma pushoutTensorι₁ [Mono f₂] (hf₁ : anodyneExtensions f₁) : anodyneExtensions h₁₂.ι := by
  refine (anodyneExtensions.arrow_mk_iso_iff ?_).1 (pushoutTensorι₂ h₁₂.flip hf₁)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _) (by simp [PushoutTensor.ι_flip])

end

lemma subcomplex_unionProd_mem_of_left {X Y : SSet.{u}}
    (A : X.Subcomplex) (B : Y.Subcomplex) (hA : anodyneExtensions A.ι) :
    anodyneExtensions (A.unionProd B).ι := by
  simpa using pushoutTensorι₁ (PushoutTensor.unionProd A B) hA

lemma subcomplex_unionProd_mem_of_right {X Y : SSet.{u}}
    (A : X.Subcomplex) (B : Y.Subcomplex) (hB : anodyneExtensions B.ι) :
    anodyneExtensions (A.unionProd B).ι :=
  (anodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (Subcomplex.unionProd.symmIso _ _) (β_ _ _))).2
    (subcomplex_unionProd_mem_of_left B A hB)

lemma pushout_desc_ι₁_whiskerRight_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    anodyneExtensions (pushout.desc (f := i) (g := ι₁) ι₁ (i ▷ Δ[1]) (by simp)) := by
  rw [← PushoutTensor.ι_horn₁₀]
  exact pushoutTensorι₂ (PushoutTensor.horn₁₀ i) (horn_ι_mem 0 1)

end anodyneExtensions

end SSet
