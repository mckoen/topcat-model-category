import TopCatModelCategory.SSet.PtSimplex

open HomotopicalAlgebra CategoryTheory Simplicial Limits Opposite

universe u

namespace SSet

namespace KanComplex

def π (n : ℕ) (X : SSet.{u}) (x : X _[0]) : Type u :=
  Subcomplex.RelativeMorphism.HomotopyClass
    (subcomplexBoundary n) (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

def π.mk {n : ℕ} {X : SSet.{u}} {x : X _[0]}
  (f : X.PtSimplex n x) : π n X x := f.homotopyClass

lemma π.mk_surjective {n : ℕ} {X : SSet.{u}} {x : X _[0]} :
    Function.Surjective (π.mk : _ → π n X x) :=
  Quot.mk_surjective

instance (n : ℕ) (X : SSet.{u}) (x : X _[0]) : One (π n X x) where
  one := Subcomplex.RelativeMorphism.const.homotopyClass

section

variable {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
  (x : X _[0]) (y : Y _[0]) (h : f.app _ x = y)

def mapπ (p : π n X x) : π n Y y :=
  p.postcomp (.ofSimplex₀ f x y h) (by rw [comp_const])

variable {Z : SSet.{u}} (g : Y ⟶ Z) (z : Z _[0]) (h' : g.app _ y = z)

lemma mapπ_mapπ (p : π n X x) :
    mapπ g n y z h' (mapπ f n x y h p) =
      mapπ (f ≫ g) n x z (by simp [h, h']) p := by
  obtain ⟨h, rfl⟩ := p.eq_homotopyClass
  rfl

lemma mapπ_comp_mapπ :
    mapπ g n y z h' ∘ mapπ f n x y h = mapπ (f ≫ g) n x z (by simp [h, h']) := by
  ext
  apply mapπ_mapπ

@[simp]
lemma mapπ_id (p : π n X x) :
    mapπ (𝟙 X) n x x rfl p = p := by
  obtain ⟨h, rfl⟩ := p.eq_homotopyClass
  rfl

def mapπEquivOfIso (e : X ≅ Y) (n : ℕ) (x : X _[0]) (y : Y _[0]) (h : e.hom.app _ x = y) :
    π n X x ≃ π n Y y where
  toFun := mapπ e.hom n x y h
  invFun := mapπ e.inv n y x (by simp [← h])
  left_inv _ := by simp [mapπ_mapπ]
  right_inv _ := by simp [mapπ_mapπ]

end

namespace π

variable {X : SSet.{u}}  {x : X _[0]} {n : ℕ} [IsFibrant X]

lemma mk_eq_mk_iff (p q : X.PtSimplex n x) :
    mk p = mk q ↔ Nonempty (p.RelStruct₀ q) := sorry

noncomputable def mul' (p q : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    X.PtSimplex (n + 1) x :=
  (PtSimplex.MulStruct.nonempty p q i).choose

noncomputable def mulStruct (p q : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    PtSimplex.MulStruct p q (mul' p q i) i :=
  (PtSimplex.MulStruct.nonempty p q i).choose_spec.some

noncomputable def mul (i : Fin (n + 1)) (g₁ g₂ : π (n + 1) X x) : π (n + 1) X x := by
  refine Quot.lift₂ (fun p q ↦ mk (mul' p q i)) ?_ ?_ g₁ g₂
  · rintro p q q' ⟨h : q.Homotopy q'⟩
    dsimp
    sorry
  · rintro p p' q ⟨h : p.Homotopy p'⟩
    dsimp
    sorry

lemma mul_mk_eq_iff {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x} {i : Fin (n + 1)} :
    mul i (mk g₁) (mk g₂) = mk g₁₂ ↔
      Nonempty (PtSimplex.MulStruct g₁ g₂ g₁₂ i) := by
  sorry

lemma mul_eq_of_mulStruct {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : PtSimplex.MulStruct g₁ g₂ g₁₂ i) : mul i (mk g₁) (mk g₂) = mk g₁₂ := by
  rw [mul_mk_eq_iff]
  exact ⟨h⟩

lemma mul_assoc (i : Fin (n + 1)) (g₁ g₂ g₃ : π (n + 1) X x) :
    mul i (mul i g₁ g₂) g₃ = mul i g₁ (mul i g₂ g₃) := by
  obtain ⟨p₁, rfl⟩ := g₁.mk_surjective
  obtain ⟨p₂, rfl⟩ := g₂.mk_surjective
  obtain ⟨p₃, rfl⟩ := g₃.mk_surjective
  exact mul_eq_of_mulStruct
    (PtSimplex.MulStruct.assoc (mulStruct p₁ p₂ i) (mulStruct p₂ p₃ i)
      (mulStruct p₁ (mul' p₂ p₃ i) i))

@[simp]
lemma one_mul (i : Fin (n + 1)) (g : π (n + 1) X x) :
    mul i 1 g = g := by
  obtain ⟨p, rfl⟩ := g.mk_surjective
  exact mul_eq_of_mulStruct (PtSimplex.MulStruct.oneMul p i)

@[simp]
lemma mul_one (i : Fin (n + 1)) (g : π (n + 1) X x) :
    mul i g 1 = g := by
  obtain ⟨p, rfl⟩ := g.mk_surjective
  exact mul_eq_of_mulStruct (PtSimplex.MulStruct.mulOne p i)

noncomputable instance : Mul (π (n + 1) X x) where
  mul := mul 0

noncomputable instance : Monoid (π (n + 1) X x) where
  mul_assoc := mul_assoc 0
  one_mul := one_mul 0
  mul_one := mul_one 0

/-
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

variable {i : Fin (n + 2)}
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

variable [IsFibrant X]

lemma exists_mulStruct
    (g₁ g₂ : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) (i : Fin (n + 1)) :
    ∃ g₁₂, Nonempty (MulStruct g₁ g₂ g₁₂ i) := by
  let φ (j : ({i.castSucc.succ}ᶜ : Set _)) :
    (subcomplexBoundary (n + 1)).RelativeMorphism _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩) :=
    if j.1 = i.succ.succ then g₁ else
      if j.1 = i.castSucc.castSucc then g₂ else .const
  obtain ⟨f, hf⟩ := exists_subcomplexHorn_desc φ
  obtain ⟨α, hα⟩ := anodyneExtensions.exists_lift_of_isFibrant f
    (anodyneExtensions.subcomplexHorn_ι_mem _ _)
  have hα' (j : Fin (n + 3)) (hj : j ≠ i.castSucc.succ) :
      standardSimplex.map (SimplexCategory.δ j) ≫ α = (φ ⟨j, hj⟩).map := by
    rw [← cancel_epi (standardSimplex.faceSingletonComplIso j).inv]
    replace hf := hf ⟨j, hj⟩
    rw [← subcomplexHorn.faceSingletonComplIso_inv_ι] at hf
    dsimp at hf
    rw [← hf, ← hα]
    rfl
  let g₁₂ : (subcomplexBoundary (n + 1)).RelativeMorphism _
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩) :=
    { map := standardSimplex.map (SimplexCategory.δ (i.castSucc.succ)) ≫ α
      comm := by
        ext j : 1
        rw [Subcomplex.ofSimplex_ι, comp_const, comp_const,
          subcomplexBoundary.ι_ι_assoc, ← Functor.map_comp_assoc]
        by_cases h : j ≤ i.castSucc
        · rw [SimplexCategory.δ_comp_δ h, Functor.map_comp_assoc, hα', δ_map]
          rw [Fin.succ_castSucc]
          rintro hj
          simp only [Fin.castSucc_inj] at hj
          simp [hj] at h
        · simp only [not_le, Fin.castSucc_lt_iff_succ_le] at h
          rw [Fin.succ_castSucc, ← SimplexCategory.δ_comp_δ h,
            Functor.map_comp_assoc, hα', δ_map]
          simp only [ne_eq, Fin.succ_inj]
          rintro rfl
          simp at h }
  refine ⟨g₁₂, ⟨{
    map := α
    h₁ := by
      rw [hα' i.succ.succ (by simp [Fin.ext_iff])]
      dsimp [φ]
      rw [if_pos rfl]
    h₂ := by
      rw [hα' i.castSucc.castSucc (by simp [Fin.ext_iff])]
      dsimp [φ]
      rw [if_neg, if_pos rfl]
      simp [Fin.ext_iff]
      omega
    h₁₂ := rfl
    h_of_lt j hj := by
      rw [hα' j (by rintro rfl; simp [Fin.lt_iff_val_lt_val] at hj)]
      dsimp [φ]
      rw [if_neg, if_neg, Subcomplex.RelativeMorphism.const_map]
      · rintro rfl
        simp [Fin.lt_iff_val_lt_val] at hj
      · rintro rfl
        simp [Fin.lt_iff_val_lt_val] at hj
        omega
    h_of_gt j hj := by
      rw [hα' j (by rintro rfl; simp [Fin.lt_iff_val_lt_val] at hj)]
      dsimp [φ]
      rw [if_neg, if_neg, Subcomplex.RelativeMorphism.const_map]
      · rintro rfl
        simp [Fin.lt_iff_val_lt_val] at hj
        omega
      · rintro rfl
        simp [Fin.lt_iff_val_lt_val] at hj }⟩⟩

lemma mk_eq_mk_iff
    (g₁ g₂ : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) :
    π.mk g₁ = π.mk g₂ ↔ Nonempty (MulStruct .const g₁ g₂ 0) := sorry

lemma mk_eq_one_iff
    (g : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) :
    π.mk g = 1 ↔ Nonempty (MulStruct .const g .const 0) := by
  apply mk_eq_mk_iff

lemma mk_eq_one_iff'
    (g : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) :
    π.mk g = 1 ↔
      ∃ (f : Δ[n + 2] ⟶ X), standardSimplex.map (SimplexCategory.δ 0) ≫ f = g.map ∧
        ∀ (i : Fin (n + 2)),
          standardSimplex.map (SimplexCategory.δ i.succ) ≫ f = const x := by
  rw [mk_eq_one_iff]
  constructor
  · rintro ⟨h⟩
    refine ⟨h.map, h.h₂, fun i ↦ ?_⟩
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · exact h.h₁₂
    · obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
      · exact h.h₁
      · exact h.h_of_gt _ (by simp [Fin.lt_iff_val_lt_val])
  · rintro ⟨f, hf₁, hf₂⟩
    exact ⟨{
      map := f
      h₁ := hf₂ 1
      h₂ := hf₁
      h₁₂ := hf₂ 0
      h_of_lt j hj := by simp at hj
      h_of_gt j hj := by
        obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by rintro rfl; simp at hj)
        exact hf₂ j }⟩

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

-/
end π

end KanComplex

end SSet
