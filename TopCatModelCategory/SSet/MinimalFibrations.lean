import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.SSet.Degenerate

universe u

open CategoryTheory HomotopicalAlgebra Simplicial MonoidalCategory
  ChosenFiniteProducts Category

namespace SSet

variable {E B : SSet.{u}} (p : E ⟶ B)

structure SimplexOverRelStruct {n : ℕ} (x y : E _[n]) where
  h : Δ[n] ⊗ Δ[1] ⟶ E
  h₀ : ι₀ ≫ h = (yonedaEquiv _ _).symm x
  h₁ : ι₁ ≫ h = (yonedaEquiv _ _).symm y
  π : Δ[n] ⟶ B
  d : ∂Δ[n] ⟶ E
  hπ : h ≫ p = fst _ _ ≫ π
  hd : (subcomplexBoundary.{u} n).ι ▷ Δ[1] ≫ h = fst _ _ ≫ d

class MinimalFibration extends Fibration p : Prop where
  minimal {n : ℕ} {x y : E _[n]} (rel : SimplexOverRelStruct p x y) : x = y

def minimalFibrations : MorphismProperty (SSet.{u}) :=
  fun _ _ p ↦ MinimalFibration p

lemma minimalFibrations_iff : minimalFibrations p ↔ MinimalFibration p := Iff.rfl

instance : MinimalFibration (𝟙 B) where
  minimal {n x y} rel := by
    apply (yonedaEquiv _ _).symm.injective
    simp only [← rel.h₀, ← rel.h₁, ← cancel_mono (𝟙 B), assoc, rel.hπ,
      lift_fst_assoc, id_comp]

instance : minimalFibrations.{u}.ContainsIdentities where
  id_mem B := by
    rw [minimalFibrations_iff]
    infer_instance

namespace SimplexOverRelStruct

attribute [reassoc] h₀ h₁ hπ hd

variable {p} {n : ℕ} {x y : E _[n]} (rel : SimplexOverRelStruct p x y)

include rel in
lemma eq [MinimalFibration p] : x = y := MinimalFibration.minimal rel

include rel in
lemma eq_of_degenerate (hx : x ∈ E.Degenerate n) (hy : y ∈ E.Degenerate n) :
    x = y := by
  obtain _ | n := n
  · simp at hx
  have h₀ := (subcomplexBoundary.{u} (n + 1)).ι ≫= rel.h₀
  have h₁ := (subcomplexBoundary.{u} (n + 1)).ι ≫= rel.h₁
  erw [← ι₀_comp_assoc, rel.hd, ι₀_fst_assoc] at h₀
  erw [← ι₁_comp_assoc, rel.hd, ι₁_fst_assoc] at h₁
  refine eq_of_degenerate_of_δ_eq hx hy (fun i ↦ ?_)
  have := subcomplexBoundary.ι i ≫= (h₀.symm.trans h₁)
  rw [subcomplexBoundary.ι_ι_assoc, subcomplexBoundary.ι_ι_assoc,
    ← yonedaEquiv_symm_map, ← yonedaEquiv_symm_map] at this
  exact (yonedaEquiv _ _).symm.injective this

noncomputable def map
    {E' B' : SSet.{u}} {p' : E' ⟶ B'} (φ : Arrow.mk p ⟶ Arrow.mk p')
    {x' y' : E' _[n]} (hx' : φ.left.app _ x = x') (hy' : φ.left.app _ y = y') :
    SimplexOverRelStruct p' x' y' where
  h := rel.h ≫ φ.left
  h₀ := by rw [rel.h₀_assoc, ← hx', yonedaEquiv_symm_comp]
  h₁ := by rw [rel.h₁_assoc, ← hy', yonedaEquiv_symm_comp]
  π := rel.π ≫ φ.right
  d := rel.d ≫ φ.left
  hπ := by
    have := Arrow.w φ
    dsimp at this
    rw [assoc, this, rel.hπ_assoc]
  hd := by rw [rel.hd_assoc]

end SimplexOverRelStruct

instance : minimalFibrations.{u}.IsStableUnderRetracts where
  of_retract {E B E' B' p p'} h (hp' : MinimalFibration p') := by
    have : Fibration p := by
      have : Fibration p' := inferInstance
      rw [fibration_iff] at this ⊢
      exact (fibrations _).of_retract h this
    constructor
    intro n x y hxy
    have h₁ := congr_arg (h.r.left.app _) ((hxy.map h.i rfl rfl).eq)
    have h₂ (a) : _ = a := congr_fun (NatTrans.congr_app h.left.retract ⟨.mk n⟩) a
    dsimp at h₂
    rw [← h₂ x, h₁, h₂]

-- to be generalized
instance : minimalFibrations.{u}.RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _
    (fun p' p e hp' ↦ (minimalFibrations).of_retract { i := e.inv, r := e.hom } hp')

end SSet
