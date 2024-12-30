import Mathlib.CategoryTheory.MorphismProperty.Limits

universe w t v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

section

variable {α : Type t} {A B : α → C} (j : ∀ i, A i ⟶ B i)
  {X₁ X₂ : C} (f : X₁ ⟶ X₂)

structure AttachCells where
  ι : Type w
  π : ι → α
  cofan₁ : Cofan (fun i ↦ A (π i))
  cofan₂ : Cofan (fun i ↦ B (π i))
  isColimit₁ : IsColimit cofan₁
  isColimit₂ : IsColimit cofan₂
  m : cofan₁.pt ⟶ cofan₂.pt
  hm (i : ι) : cofan₁.inj i ≫ m = j (π i) ≫ cofan₂.inj i
  g₁ : cofan₁.pt ⟶ X₁
  g₂ : cofan₂.pt ⟶ X₂
  isPushout : IsPushout g₁ m f g₂

namespace AttachCells

open MorphismProperty

variable {j f} (c : AttachCells.{w} j f)

include c

lemma pushouts_coproducts : (coproducts.{w} (ofHoms j)).pushouts f := by
  refine ⟨_, _, _, _, _, ?_, c.isPushout⟩
  have : c.m = c.isColimit₁.desc
      (Cocone.mk _ (Discrete.natTrans (fun ⟨i⟩ ↦ by exact j (c.π i)) ≫ c.cofan₂.ι)) :=
    c.isColimit₁.hom_ext (fun ⟨i⟩ ↦ by rw [IsColimit.fac]; exact c.hm i)
  rw [this, coproducts_iff]
  exact ⟨c.ι, ⟨_, _, _, _, c.isColimit₁, c.isColimit₂, _, fun i ↦ ⟨_⟩⟩⟩

-- the map for the cell corresponding to `i : c.ι`
def cell (i : c.ι) : B (c.π i) ⟶ X₂ := c.cofan₂.inj i ≫ c.g₂

lemma cell_def (i : c.ι) : c.cell i = c.cofan₂.inj i ≫ c.g₂ := rfl

lemma hom_ext {Z : C} {φ φ' : X₂ ⟶ Z}
    (h₀ : f ≫ φ = f ≫ φ') (h : ∀ i, c.cell i ≫ φ = c.cell i ≫ φ') :
    φ = φ' := by
  apply c.isPushout.hom_ext h₀
  apply Cofan.IsColimit.hom_ext c.isColimit₂
  simpa [cell_def] using h

end AttachCells

open MorphismProperty in
lemma nonempty_attachCells_iff :
    Nonempty (AttachCells.{w} j f) ↔ (coproducts.{w} (ofHoms j)).pushouts f := by
  constructor
  · rintro ⟨c⟩
    exact c.pushouts_coproducts
  · rintro ⟨Y₁, Y₂, m, g₁, g₂, h, sq⟩
    obtain ⟨m', hm'⟩ : ∃ m', m' = m := ⟨_, rfl⟩
    rw [coproducts_iff, ← hm'] at h
    obtain ⟨ι, ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩⟩ := h
    let Y₁ (i : ι) : C := F₁.obj ⟨i⟩
    let Y₂ (i : ι) : C := F₂.obj ⟨i⟩
    let ψ (i : ι) : Y₁ i ⟶ Y₂ i := φ.app ⟨i⟩
    let π (i : ι) : α := ((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose
    let e (i : ι) : Arrow.mk (ψ i) ≅ Arrow.mk (j (π i)) :=
      eqToIso (((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose_spec)
    let e₁ (i : ι) : Y₁ i ≅ A (π i) := Arrow.leftFunc.mapIso (e i)
    let e₂ (i : ι) : Y₂ i ≅ B (π i) := Arrow.rightFunc.mapIso (e i)
    exact ⟨{
        ι := ι
        π := π
        cofan₁ := Cofan.mk c₁.pt (fun i ↦ (e₁ i).inv ≫ c₁.ι.app ⟨i⟩)
        cofan₂ := Cofan.mk c₂.pt (fun i ↦ (e₂ i).inv ≫ c₂.ι.app ⟨i⟩)
        isColimit₁ :=
          (IsColimit.precomposeHomEquiv (Discrete.natIso (fun ⟨i⟩ ↦ e₁ i)) _).1
            (IsColimit.ofIsoColimit h₁ (Cocones.ext (Iso.refl _) (by simp)))
        isColimit₂ :=
          (IsColimit.precomposeHomEquiv (Discrete.natIso (fun ⟨i⟩ ↦ e₂ i)) _).1
            (IsColimit.ofIsoColimit h₂ (Cocones.ext (Iso.refl _) (by simp)))
        hm i := by
          have eq₁ := c₁.ι.app ⟨i⟩ ≫= hm'
          have eq₂ := (e i).inv.w
          rw [IsColimit.fac] at eq₁
          dsimp [e₁, e₂] at eq₁ eq₂ ⊢
          rw [Category.assoc, ← eq₁, reassoc_of% eq₂]
        isPushout := sq }⟩

end

end HomotopicalAlgebra
