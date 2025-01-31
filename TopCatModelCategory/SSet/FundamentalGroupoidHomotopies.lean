import TopCatModelCategory.SSet.FundamentalGroupoid
import TopCatModelCategory.SSet.Square

universe u

open HomotopicalAlgebra CategoryTheory MonoidalCategory Simplicial

namespace SSet

variable {X : SSet.{u}}

namespace KanComplex

namespace FundamentalGroupoid

variable {x₀ x₁ x₂ : FundamentalGroupoid X}

namespace Path

def HomotopyL (p q : Path x₀ x₁) := CompStruct p (Path.id x₁) q
def HomotopyR (p q : Path x₀ x₁) := CompStruct (Path.id x₀) p q

section

variable (p q r : Path x₀ x₁)

def HomotopyL.refl : HomotopyL p p := CompStruct.compId p
def HomotopyR.refl : HomotopyR p p := CompStruct.idComp p

variable {p q r} [IsFibrant X]

noncomputable def HomotopyL.symm (h : HomotopyL p q) : HomotopyL q p :=
  CompStruct.assoc h (CompStruct.compId _) (CompStruct.compId p)

noncomputable def HomotopyR.symm (h : HomotopyR p q) : HomotopyR q p :=
  CompStruct.assoc' (CompStruct.idComp _) h (CompStruct.idComp p)

noncomputable def HomotopyL.homotopyR (h : HomotopyL p q) : HomotopyR p q :=
  HomotopyR.symm (CompStruct.assoc' (CompStruct.idComp p) h (CompStruct.compId p))

noncomputable def HomotopyR.homotopyL (h : HomotopyR p q) : HomotopyL p q :=
  HomotopyL.symm (CompStruct.assoc h (CompStruct.compId p) (CompStruct.idComp p))

noncomputable def HomotopyL.trans (h : HomotopyL p q) (h' : HomotopyL q r) :
    HomotopyL p r :=
  CompStruct.assoc (CompStruct.idComp p) h h'.homotopyR

noncomputable def HomotopyR.trans (h : HomotopyR p q) (h' : HomotopyR q r) :
    HomotopyR p r :=
  CompStruct.assoc' h (CompStruct.compId p) h'.homotopyL

end

namespace CompStruct

variable [IsFibrant X]

noncomputable def unique {p₀₁ : Path x₀ x₁} {p₁₂ : Path x₁ x₂} {p₀₂ : Path x₀ x₂}
    (h : CompStruct p₀₁ p₁₂ p₀₂)
    {p₀₁' : Path x₀ x₁} {p₁₂' : Path x₁ x₂} {p₀₂' : Path x₀ x₂}
    (h' : CompStruct p₀₁' p₁₂' p₀₂')
    (h₀₁ : HomotopyL p₀₁ p₀₁') (h₁₂ : HomotopyL p₁₂ p₁₂') :
    HomotopyL p₀₂ p₀₂' :=
  assoc h (compId p₁₂) (assoc (compId p₀₁) h₁₂.homotopyR (assoc' h₀₁ (idComp p₁₂') h'))

end CompStruct

namespace Homotopy

variable {p q : Path x₀ x₁} (h : Homotopy p q)

lemma h_app_zero_of_fst_zero (x : Δ[1] _[0]) :
    h.h.app _ (⟨standardSimplex.obj₀Equiv.symm 0, x⟩) = x₀.pt := by
  have := (standardSimplex.leftUnitor _).inv ≫= subcomplexBoundary₁.ι₀ ▷ _ ≫= h.rel
  rw [Category.assoc, ChosenFiniteProducts.whiskerRight_fst_assoc,
    subcomplexBoundary₁.ι₀_desc_assoc, yonedaEquiv_symm_zero, const_comp,
    FunctorToTypes.comp, Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe,
    comp_const, comp_const, ← comp_whiskerRight_assoc,
    subcomplexBoundary₁.ι₀_ι, standardSimplex.leftUnitor_inv_map_δ_one_assoc] at this
  replace this := congr_fun (NatTrans.congr_app this _) x
  dsimp at this
  rw [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply] at this
  exact this

lemma h_app_zero_of_fst_one (x : Δ[1] _[0]) :
    h.h.app _ (⟨standardSimplex.obj₀Equiv.symm 1, x⟩) = x₁.pt := by
  have := (standardSimplex.leftUnitor _).inv ≫= subcomplexBoundary₁.ι₁ ▷ _ ≫= h.rel
  rw [Category.assoc, ChosenFiniteProducts.whiskerRight_fst_assoc,
    subcomplexBoundary₁.ι₁_desc_assoc, yonedaEquiv_symm_zero, const_comp,
    FunctorToTypes.comp, Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe,
    comp_const, comp_const, ← comp_whiskerRight_assoc,
    subcomplexBoundary₁.ι₁_ι, standardSimplex.leftUnitor_inv_map_δ_zero_assoc] at this
  replace this := congr_fun (NatTrans.congr_app this _) x
  dsimp at this
  rw [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply] at this
  exact this

@[simp]
lemma h_app_obj₀Equiv_zero :
    h.h.app _ (prodStandardSimplex.obj₀Equiv.symm 0) = x₀.pt := by
  apply h_app_zero_of_fst_zero

@[simp]
lemma h_app_obj₀Equiv_one :
    h.h.app _ (prodStandardSimplex.obj₀Equiv.symm 1) = x₁.pt := by
  apply h_app_zero_of_fst_one

noncomputable abbrev diagonal : Path x₀ x₁ :=
  Path.mk (square.diagonal ≫ h.h) (by simp) (by simp)

noncomputable def homotopyLDiagonal : HomotopyL p h.diagonal where
  map := square.ιTriangle₀ ≫ h.h
  h₀₁ := by rw [← h.h₀, square.δ₂_ιTriangle₀_assoc]

noncomputable def homotopyRDiagonal : HomotopyR q h.diagonal where
  map := square.ιTriangle₁ ≫ h.h

noncomputable def homotopyL [IsFibrant X] : HomotopyL p q :=
  h.homotopyLDiagonal.trans h.homotopyRDiagonal.homotopyL.symm

noncomputable def homotopyR [IsFibrant X] : HomotopyR p q :=
  h.homotopyL.homotopyR

end Homotopy

end Path

end FundamentalGroupoid

end KanComplex

end SSet
