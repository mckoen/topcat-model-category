import TopCatModelCategory.SSet.AnodyneExtensions
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

universe u

open CategoryTheory MonoidalCategory Limits Simplicial

namespace SSet

section

variable {A₁ A₂ B₁ B₂ : SSet.{u}} (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂)

def PushoutTensor := Functor.PushoutObjObj (curriedTensor SSet.{u}) f₁ f₂

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

end PushoutTensor

end

namespace anodyneExtensions


section

variable {A₁ A₂ B₁ B₂ : SSet.{u}} {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂}
  (h : PushoutTensor f₁ f₂)

lemma pushoutTensor₁ (hf₁ : anodyneExtensions f₁) : anodyneExtensions h.ι := sorry

lemma pushoutTensor₂ (hf₂ : anodyneExtensions f₂) : anodyneExtensions h.ι := by
  refine (anodyneExtensions.arrow_mk_iso_iff ?_).1 (pushoutTensor₁ h.flip hf₂)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _) (by simp [PushoutTensor.ι_flip])

end

lemma subcomplex_unionProd_mem_of_left {X Y : SSet.{u}}
    (A : X.Subcomplex) (B : Y.Subcomplex) (hA : anodyneExtensions A.ι) :
    anodyneExtensions (A.unionProd B).ι := by
  simpa using pushoutTensor₁ (PushoutTensor.unionProd A B) hA

lemma subcomplex_unionProd_mem_of_right {X Y : SSet.{u}}
    (A : X.Subcomplex) (B : Y.Subcomplex) (hB : anodyneExtensions B.ι) :
    anodyneExtensions (A.unionProd B).ι :=
  (anodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (Subcomplex.unionProd.symmIso _ _) (β_ _ _))).2
    (subcomplex_unionProd_mem_of_left B A hB)

lemma pushout_desc_ι₁_whiskerRight_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    anodyneExtensions (pushout.desc (f := i) (g := ι₁) ι₁ (i ▷ Δ[1]) (by simp)) := by
  sorry

end anodyneExtensions

end SSet
