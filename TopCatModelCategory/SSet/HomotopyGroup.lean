import TopCatModelCategory.SSet.Homotopy

open HomotopicalAlgebra CategoryTheory Simplicial Limits Opposite

universe u

namespace SSet

namespace KanComplex

namespace π

variable {X : SSet.{u}} {x : X _[0]} {n : ℕ}

@[reassoc]
lemma comp_map_eq_const
    (s : Subcomplex.RelativeMorphism (subcomplexBoundary n) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩))
    {Y : SSet.{u}} (φ : Y ⟶ Δ[n]) [Y.HasDimensionLT n] :
    φ ≫ s.map = const x := by
  refine (Subcomplex.lift φ ?_) ≫= s.comm
  apply le_antisymm (by simp)
  rw [← Subcomplex.image_le_iff, Subcomplex.image_top,
    standardSimplex.subcomplex_le_boundary_iff]
  intro h
  replace h : standardSimplex.id n ∈ (Subcomplex.range φ).obj _ := by simp [h]
  obtain ⟨x, hx⟩ := h
  have : ¬ (x ∈ Y.Degenerate n) := by
    intro hx'
    have := degenerate_map hx' φ
    simp [hx, mem_degenerate_iff_non_mem_nondegenerate,
      standardSimplex.non_degenerate_top_dim] at this
  simp [Y.degenerate_eq_top_of_hasDimensionLT n n (by rfl)] at this

@[reassoc (attr := simp)]
lemma δ_map (s : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) (i : Fin (n + 2)) :
    standardSimplex.map (SimplexCategory.δ i) ≫ s.map = const x :=
  comp_map_eq_const _ _

section

variable (i : Fin (n + 2))
  (φ : ({i}ᶜ : Set _) → Subcomplex.RelativeMorphism (subcomplexBoundary n) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩))

lemma exists_subcomplexHorn_desc :
    ∃ (f : Λ[(n + 1), i] ⟶ X), ∀ (j : ({i}ᶜ : Set _)),
      subcomplexHorn.faceι i j.1 j.2 ≫ f =
        (standardSimplex.faceSingletonComplIso j.1).inv ≫ (φ j).map :=
  ⟨(subcomplexHorn.isColimit.{u} i).desc (Multicofork.ofπ _ _
      (fun j ↦ (standardSimplex.faceSingletonComplIso j.1).inv ≫ (φ j).map) (by
        rintro ⟨⟨j, j'⟩, hjj'⟩
        simp only [Set.mem_setOf_eq] at hjj'
        dsimp
        rw [← Category.assoc, ← Category.assoc]
        let S : Finset (Fin (n + 2)) := {j.1, j'.1}
        have hS : S.card = 2 := Finset.card_pair (fun h ↦ by
          rw [← Subtype.ext_iff] at h
          simp [h] at hjj')
        have : HasDimensionLT (Subpresheaf.toPresheaf (standardSimplex.face.{u}
            (Sᶜ : Finset (Fin (n + 2))))) n := by
          apply standardSimplex.face_hasDimensionLT
          rw [← Nat.add_le_add_iff_right (n := S.card),
            Finset.card_compl_add_card, Fintype.card_fin, hS]
        rw [comp_map_eq_const, comp_map_eq_const])),
    fun j ↦ (subcomplexHorn.isColimit i).fac _ (.right j)⟩

end

structure MulStruct
    (g₁ g₂ g₁₂ : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩))
      (i : Fin (n + 1)) where
  map : Δ[n + 2] ⟶ X
  h₁ : standardSimplex.map (SimplexCategory.δ (i.succ.succ)) ≫ map = g₁.map
  h₂ : standardSimplex.map (SimplexCategory.δ (i.castSucc.castSucc)) ≫ map = g₂.map
  h_of_lt (j : Fin (n + 3)) (hj : j < i.castSucc.castSucc) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x
  h_of_gt (j : Fin (n + 3)) (hj : i.succ.succ < j) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x
  h₁₂ : standardSimplex.map (SimplexCategory.δ (i.castSucc.succ)) ≫ map = g₁₂.map

namespace MulStruct

def mulOne (g : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) (i : Fin (n + 1)) :
      MulStruct g .const g i where
  map := standardSimplex.map (SimplexCategory.σ i.succ) ≫ g.map
  h₁ := by
    rw [← Functor.map_comp_assoc, SimplexCategory.δ_comp_σ_succ,
      CategoryTheory.Functor.map_id, Category.id_comp]
  h₂ := by
    simp [← Functor.map_comp_assoc,
      SimplexCategory.δ_comp_σ_of_le (i := i.castSucc) (j := i) (by rfl)]
  h₁₂ := by
    rw [← Functor.map_comp_assoc, Fin.succ_castSucc, SimplexCategory.δ_comp_σ_self,
      CategoryTheory.Functor.map_id, Category.id_comp]
  h_of_lt j hj := by
    have hj' : j ≠ Fin.last _ := by
      rintro rfl
      rw [Fin.lt_iff_val_lt_val, Fin.val_last, Fin.coe_castSucc] at hj
      omega
    have := SimplexCategory.δ_comp_σ_of_le (i := j.castPred hj') (j := i) hj.le
    rw [Fin.castSucc_castPred] at this
    simp [← Functor.map_comp_assoc, this]
  h_of_gt j hj := by
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by rintro rfl; simp at hj)
    have := SimplexCategory.δ_comp_σ_of_gt (i := j) (j := i.succ.castPred (fun h ↦ by
      rw [h, Fin.lt_iff_val_lt_val] at hj
      dsimp at hj
      omega))
      (by simpa using hj)
    simp only [Fin.castSucc_castPred] at this
    simp [← Functor.map_comp_assoc, this]

def oneMul (g : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) (i : Fin (n + 1)) :
      MulStruct .const g g i where
  map := standardSimplex.map (SimplexCategory.σ i.castSucc) ≫ g.map
  h₁ := by
    rw [← Functor.map_comp_assoc, SimplexCategory.δ_comp_σ_of_gt (by simp)]
    simp
  h₂ := by
    rw [← Functor.map_comp_assoc, SimplexCategory.δ_comp_σ_self]
    simp
  h₁₂ := by
    rw [← Functor.map_comp_assoc, SimplexCategory.δ_comp_σ_succ]
    simp
  h_of_lt j hj := by
    have hj' : j ≠ Fin.last _ := fun hj' ↦ by
      simp only [hj', Fin.lt_iff_val_lt_val, Fin.val_last, Fin.coe_castSucc] at hj
      omega
    obtain ⟨i, rfl⟩ := i.eq_succ_of_ne_zero (by rintro rfl; simp at hj)
    have this := SimplexCategory.δ_comp_σ_of_le (i := j.castPred hj')
      (j := i.castSucc) (by
        simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ] at hj
        simp only [Fin.le_iff_val_le_val, Fin.coe_castPred, Fin.coe_castSucc]
        omega)
    rw [Fin.castSucc_castPred] at this
    simp [← Functor.map_comp_assoc, ← Fin.succ_castSucc, this]
  h_of_gt j hj := by
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by rintro rfl; simp at hj)
    simp only [Fin.succ_lt_succ_iff] at hj
    simp [← Functor.map_comp_assoc,
      SimplexCategory.δ_comp_σ_of_gt (i.castSucc_lt_succ.trans hj)]

end MulStruct

lemma exists_mulStruct
    (g₁ g₂ : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) (i : Fin (n + 1)) :
    ∃ g₁₂, Nonempty (MulStruct g₁ g₂ g₁₂ i) := by
  sorry

noncomputable def mul'
    (g₁ g₂ : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) :
    Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩) :=
  (exists_mulStruct g₁ g₂ 0).choose

noncomputable def mulStruct (g₁ g₂ : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) :
      MulStruct g₁ g₂ (mul' g₁ g₂) 0 :=
  (exists_mulStruct g₁ g₂ 0).choose_spec.some

noncomputable instance : Mul (π (n + 1) X x) where
  mul := Quot.lift₂ (fun g₁ g₂ ↦ (mul' g₁ g₂).homotopyClass) sorry sorry

lemma MulStruct.eq₀ {g₁ g₂ g₁₂ : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)} (h : MulStruct g₁ g₂ g₁₂ 0) :
    π.mk g₁ * π.mk g₂ = π.mk g₁₂ := sorry

noncomputable instance : Monoid (π (n + 1) X x) where
  mul_assoc := sorry
  one_mul γ := by
    obtain ⟨g, rfl⟩ := γ.mk_surjective
    exact (MulStruct.oneMul g 0).eq₀
  mul_one γ := by
    obtain ⟨g, rfl⟩ := γ.mk_surjective
    exact (MulStruct.mulOne g 0).eq₀

end π

end KanComplex

end SSet
