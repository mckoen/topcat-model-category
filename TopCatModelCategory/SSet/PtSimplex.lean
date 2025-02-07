import TopCatModelCategory.SSet.Horn
import TopCatModelCategory.SSet.HomotopyBasic
import TopCatModelCategory.SSet.FundamentalGroupoid

universe u

open HomotopicalAlgebra CategoryTheory Simplicial Limits

namespace SSet

variable (X : SSet.{u})

abbrev PtSimplex (n : ℕ) (x : X _[0]) : Type u :=
  Subcomplex.RelativeMorphism
    (subcomplexBoundary n) (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

namespace PtSimplex

variable {X} {n : ℕ} {x : X _[0]}

@[simps]
def mk (f : Δ[n + 1] ⟶ X)
    (hf : ∀ i, standardSimplex.map (SimplexCategory.δ i) ≫ f = const x) :
    X.PtSimplex (n +1) x where
  map := f
  comm := by
    ext i : 1
    rw [Subcomplex.ofSimplex_ι, subcomplexBoundary.ι_ι_assoc, hf _, comp_const, comp_const]

def equiv₀ : X.PtSimplex 0 x ≃ X _[0] where
  toFun f := yonedaEquiv _ _ f.map
  invFun y :=
    { map := (yonedaEquiv _ _).symm y
      comm := by
        ext _ ⟨x, hx⟩
        simp at hx }
  left_inv f := by simp
  right_inv y := by simp only [Equiv.apply_symm_apply]

section

@[reassoc]
lemma comp_map_eq_const
    (s : X.PtSimplex n x)
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
lemma δ_map (f : X.PtSimplex (n + 1) x) (i : Fin (n + 2)) :
    standardSimplex.map (SimplexCategory.δ i) ≫ f.map = const x :=
  comp_map_eq_const _ _

end

structure RelStruct (f g : X.PtSimplex n x) (i : Fin (n + 1)) where
  map : Δ[n + 1] ⟶ X
  δ_castSucc_map : standardSimplex.map (SimplexCategory.δ i.castSucc) ≫ map = f.map := by aesop_cat
  δ_succ_map : standardSimplex.map (SimplexCategory.δ i.succ) ≫ map = g.map := by aesop_cat
  δ_map_of_lt (j : Fin (n + 2)) (hj : j < i.castSucc) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x := by aesop_cat
  δ_map_of_gt (j : Fin (n + 2)) (hj : i.succ < j) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x := by aesop_cat

def RelStruct₀ (f g : X.PtSimplex n x) := RelStruct f g 0

namespace RelStruct₀

def equiv₀ {f g : X.PtSimplex 0 x} :
    RelStruct₀ f g ≃
  KanComplex.FundamentalGroupoid.Edge (X := X) ⟨equiv₀ g⟩ ⟨equiv₀ f⟩ := sorry

end RelStruct₀

structure MulStruct (f g fg : X.PtSimplex n x) (i : Fin n) where
  map : Δ[n + 1] ⟶ X
  δ_succ_succ_map : standardSimplex.map (SimplexCategory.δ (i.succ.succ)) ≫ map = f.map :=
    by aesop_cat
  δ_castSucc_castSucc_map : standardSimplex.map
    (SimplexCategory.δ (i.castSucc.castSucc)) ≫ map = g.map := by aesop_cat
  δ_castSucc_succ_map : standardSimplex.map (SimplexCategory.δ (i.castSucc.succ)) ≫ map =
    fg.map := by aesop_cat
  δ_map_of_lt (j : Fin (n + 2)) (hj : j < i.castSucc.castSucc) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x := by aesop_cat
  δ_map_of_gt (j : Fin (n + 2)) (hj : i.succ.succ < j) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x := by aesop_cat

namespace RelStruct

attribute [reassoc (attr := simp)] δ_castSucc_map δ_succ_map
  δ_map_of_lt δ_map_of_gt

def refl (f : X.PtSimplex n x) (i : Fin (n + 1)) : RelStruct f f i where
  map := standardSimplex.map (SimplexCategory.σ i) ≫ f.map
  δ_castSucc_map := by
    simp [← Functor.map_comp_assoc, SimplexCategory.δ_comp_σ_self]
  δ_succ_map := by
    simp [← Functor.map_comp_assoc, SimplexCategory.δ_comp_σ_succ]
  δ_map_of_lt j hj := by
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · simp at hj
    . obtain ⟨j, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
      · obtain _ | n := n
        · fin_cases i
        · rw [← Functor.map_comp_assoc,
            SimplexCategory.δ_comp_σ_of_le
            (by simpa only[← Fin.succ_castSucc,
              Fin.castSucc_lt_succ_iff] using hj),
            Functor.map_comp_assoc, δ_map, comp_const]
      · have := Fin.ne_last_of_lt hj
        simp at this
  δ_map_of_gt j hj := by
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · obtain _ | n := n
      · fin_cases i
      · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
        · simp at hj
        · rw [← Functor.map_comp_assoc,
            SimplexCategory.δ_comp_σ_of_gt (by simpa using hj),
            Functor.map_comp_assoc, δ_map, comp_const]
    · simp only [Fin.succ_last, Nat.succ_eq_add_one] at hj
      have := Fin.ne_last_of_lt hj
      simp at this

end RelStruct

namespace MulStruct

attribute [reassoc (attr := simp)] δ_succ_succ_map δ_castSucc_castSucc_map
  δ_castSucc_succ_map δ_map_of_lt δ_map_of_gt

end MulStruct

def relStructCastSuccEquivMulStruct {f g : X.PtSimplex n x} {i : Fin n} :
    RelStruct f g i.castSucc ≃ MulStruct .const f g i where
  toFun h :=
    { map := h.map
      δ_succ_succ_map := h.δ_map_of_gt i.succ.succ (by simp)
      δ_map_of_gt j hj := h.δ_map_of_gt j (lt_trans (by simp) hj) }
  invFun h :=
    { map := h.map
      δ_map_of_gt j hj := by
        rw [Fin.succ_castSucc, Fin.castSucc_lt_iff_succ_le] at hj
        obtain rfl | hj := hj.eq_or_lt
        · exact h.δ_succ_succ_map
        · exact h.δ_map_of_gt j hj }
  left_inv _ := rfl
  right_inv _ := rfl

def relStructSuccEquivMulStruct {f g : X.PtSimplex n x} {i : Fin n} :
    RelStruct f g i.succ ≃ MulStruct g .const f i where
  toFun h :=
    { map := h.map
      δ_castSucc_succ_map := h.δ_castSucc_map
      δ_map_of_lt j hj := h.δ_map_of_lt j (lt_trans hj (by simp)) }
  invFun h :=
    { map := h.map
      δ_castSucc_map := h.δ_castSucc_succ_map
      δ_map_of_lt j hj := by
        rw [← Fin.succ_castSucc] at hj
        obtain rfl | hj := (Fin.le_castSucc_iff.2 hj).eq_or_lt
        · exact h.δ_castSucc_castSucc_map
        · exact h.δ_map_of_lt j hj }
  left_inv _ := rfl
  right_inv _ := rfl

namespace MulStruct

def oneMul (f : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    MulStruct .const f f i :=
  relStructCastSuccEquivMulStruct (RelStruct.refl f i.castSucc)

def mulOne (f : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    MulStruct f .const f i :=
  relStructSuccEquivMulStruct (RelStruct.refl f i.succ)

variable [IsFibrant X]

noncomputable def assoc
    {f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f₀₃ : X.PtSimplex n x} {i : Fin n}
    (h₀₂ : MulStruct f₀₁ f₁₂ f₀₂ i) (h₁₃ : MulStruct f₁₂ f₂₃ f₁₃ i)
    (h : MulStruct f₀₁ f₁₃ f₀₃ i) :
    MulStruct f₀₂ f₂₃ f₀₃ i := by
  apply Nonempty.some
  let α (j : ({i.succ.castSucc.castSucc}ᶜ : Set (Fin (n + 3)))) : Δ[n + 1] ⟶ X :=
    if j.1 = i.castSucc.castSucc.castSucc then h₁₃.map else
      if j.1 = i.castSucc.succ.succ then h.map else
        if j.1 = i.succ.succ.succ then h₀₂.map else
          const x
  have hα₀ (j : ({i.succ.castSucc.castSucc}ᶜ : Set (Fin (n + 3))))
      (hα : j.1 < i.castSucc.castSucc.castSucc) : α j = const x := by
    dsimp [α]
    rw [if_neg, if_neg, if_neg]
    all_goals
      simp [Fin.lt_iff_val_lt_val, Fin.ext_iff] at hα ⊢
      omega
  have hα₁ : α ⟨i.castSucc.castSucc.castSucc, by simp [Fin.ext_iff]⟩ = h₁₃.map := if_pos rfl
  have hα₂ : α ⟨i.castSucc.succ.succ, by simp [Fin.ext_iff]⟩ = h.map := by
    dsimp [α]
    rw [if_neg, if_pos rfl]
    simp [Fin.ext_iff]
    omega
  have hα₃ : α ⟨i.succ.succ.succ, by simp [Fin.ext_iff]; omega⟩ = h₀₂.map := by
    dsimp [α]
    rw [if_neg, if_neg, if_pos rfl] <;> simp [Fin.ext_iff]; omega
  have hα₄ (j : ({i.succ.castSucc.castSucc}ᶜ : Set (Fin (n + 3))))
      (hα : i.succ.succ.succ < j) : α j = const x := by
    dsimp [α]
    rw [if_neg, if_neg, if_neg]
    simp [Fin.ext_iff]
    all_goals
      simp [Fin.lt_iff_val_lt_val, Fin.ext_iff] at hα ⊢
      omega
  obtain ⟨β, hβ⟩ := subcomplexHorn.exists_desc α (by
    rintro ⟨j, hj⟩ ⟨k, hk⟩ hjk
    dsimp at hjk
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hj hk
    by_cases hk₁ : k < i.castSucc.castSucc.castSucc
    · rw [hα₀ _ (hjk.trans hk₁), hα₀ _ hk₁, comp_const, comp_const]
    · simp only [not_lt] at hk₁
      obtain hk₁ | rfl := hk₁.lt_or_eq; swap
      · rw [hα₁, hα₀ _ hjk, h₁₃.δ_map_of_lt _ hjk, comp_const]
      · rw [Fin.castSucc_lt_iff_succ_le] at hk₁
        obtain hk₁ | rfl := hk₁.lt_or_eq; swap
        · exact (hk rfl).elim
        · rw [Fin.succ_castSucc, Fin.castSucc_lt_iff_succ_le] at hk₁
          obtain hk₁ | rfl := hk₁.lt_or_eq; swap
          · rw [hα₂]
            by_cases hj₁ : j < i.castSucc.castSucc.castSucc
            · rw [hα₀ _ hj₁, comp_const, h.δ_map_of_lt _ hj₁]
            · simp only [not_lt] at hj₁
              obtain rfl | hj₁ := hj₁.eq_or_lt
              · simp [hα₁]
              · rw [← Fin.succ_le_castSucc_iff,
                  ← Fin.succ_castSucc, Fin.succ_le_succ_iff] at hjk
                obtain hjk | rfl := hjk.lt_or_eq
                · rw [← Fin.succ_castSucc, ← Fin.le_castSucc_iff] at hjk
                  omega
                · exact (hj rfl).elim
          · rw [Fin.succ_castSucc, Fin.succ_castSucc,
              Fin.castSucc_lt_iff_succ_le] at hk₁
            obtain hk₁ | rfl := hk₁.lt_or_eq; swap
            · rw [hα₃, Fin.pred_succ]
              rw [← Fin.le_castSucc_iff] at hjk
              obtain hjk | rfl := hjk.lt_or_eq; swap
              · rw [Fin.castPred_castSucc, δ_succ_succ_map]
                simp only [← Fin.succ_castSucc, hα₂,
                  δ_succ_succ_map]
              · rw [← Fin.succ_castSucc, ← Fin.le_castSucc_iff] at hjk
                obtain hjk | rfl := hjk.lt_or_eq; swap
                · exact (hj rfl).elim
                · rw [← Fin.succ_castSucc, ← Fin.succ_castSucc, ← Fin.le_castSucc_iff] at hjk
                  obtain hjk | rfl := hjk.lt_or_eq; swap
                  · simp [hα₁]
                  · rw [hα₀ _ hjk, comp_const, h₀₂.δ_map_of_lt _ hjk]
            · rw [hα₄ ⟨k, _⟩ hk₁, comp_const]
              by_cases hj₁ : i.succ.succ.succ < j
              · rw [hα₄ _ hj₁, comp_const]
              · simp only [not_lt] at hj₁
                obtain hj₁ | rfl := hj₁.lt_or_eq; swap
                · rw [hα₃]
                  apply h₀₂.δ_map_of_gt
                  rw [← Fin.succ_lt_succ_iff, Fin.succ_pred]
                  exact hjk
                · rw [← Fin.le_castSucc_iff] at hj₁
                  obtain hj₁ | rfl := hj₁.lt_or_eq; swap
                  · simp only [← Fin.succ_castSucc, hα₂]
                    apply h.δ_map_of_gt
                    rw [← Fin.succ_lt_succ_iff, Fin.succ_pred]
                    exact hk₁
                  · rw [← Fin.succ_castSucc, ← Fin.le_castSucc_iff] at hj₁
                    obtain hj₁ | rfl := hj₁.lt_or_eq; swap
                    · exact (hj rfl).elim
                    · rw [← Fin.succ_castSucc, ← Fin.succ_castSucc,
                        ← Fin.le_castSucc_iff] at hj₁
                      obtain hj₁ | rfl := hj₁.lt_or_eq; swap
                      · rw [hα₁]
                        apply h₁₃.δ_map_of_gt
                        rw [← Fin.succ_lt_succ_iff, Fin.succ_pred]
                        exact hk₁
                      · rw [hα₀ _ hj₁, comp_const])
  obtain ⟨γ, hγ⟩ := anodyneExtensions.exists_lift_of_isFibrant β
    (anodyneExtensions.subcomplexHorn_ι_mem _ _)
  replace hγ (j : Fin (n + 3)) (hj : j ≠ i.succ.castSucc.castSucc) :
      standardSimplex.map (SimplexCategory.δ j) ≫ γ = α ⟨j, hj⟩ := by
    rw [← hβ ⟨j, hj⟩, ← hγ, subcomplexHorn.ι_ι_assoc]
  let μ := standardSimplex.map (SimplexCategory.δ i.succ.castSucc.castSucc) ≫ γ
  have hμ (j : Fin (n + 2)) (hj : j ≤ i.castSucc.castSucc) :
      standardSimplex.map (SimplexCategory.δ j) ≫ μ =
        standardSimplex.map (SimplexCategory.δ i.castSucc.castSucc) ≫
          α ⟨j.castSucc, by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Fin.castSucc_inj]
            rintro rfl
            simp at hj⟩ := by
    dsimp [μ]
    conv_lhs =>
      rw [← Functor.map_comp_assoc, ← Fin.succ_castSucc,
        ← Fin.succ_castSucc, SimplexCategory.δ_comp_δ hj,
        Functor.map_comp_assoc, hγ _ (by
          simp only [ne_eq, Fin.castSucc_inj, μ]
          rintro rfl
          simp at hj)]
  have hμ' (j : Fin (n + 2)) (hj : i.succ.castSucc ≤ j) :
      standardSimplex.map (SimplexCategory.δ j) ≫ μ =
        standardSimplex.map (SimplexCategory.δ i.succ.castSucc) ≫
          α ⟨j.succ, by
            simp [← Fin.succ_castSucc]
            rintro rfl
            simp at hj⟩ := by
    dsimp [μ]
    conv_lhs =>
      rw [← Functor.map_comp_assoc,
        ← SimplexCategory.δ_comp_δ hj, Functor.map_comp_assoc]
    rw [hγ]
  refine ⟨{
      map := μ
      δ_succ_succ_map := by
        rw [hμ' _ i.succ.castSucc_le_succ, hα₃]
        exact h₀₂.δ_castSucc_succ_map
      δ_castSucc_castSucc_map := by
        rw [hμ _ (by rfl), hα₁]
        exact h₁₃.δ_castSucc_castSucc_map
      δ_castSucc_succ_map := by
        rw [hμ' _ (by rfl), hα₂]
        exact h.δ_castSucc_succ_map
      δ_map_of_lt j hj := by
        rw [hμ _ (by omega), hα₀ _ (by simpa using hj), comp_const]
      δ_map_of_gt j hj := by
        rw [hμ' _ (le_trans
            (by simpa [← Fin.succ_castSucc] using i.castSucc_le_succ) hj.le),
          hα₄ _ (by simpa), comp_const]
  }⟩

noncomputable def assoc'
    {f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f₀₃ : X.PtSimplex n x} {i : Fin n}
    (h₀₂ : MulStruct f₀₁ f₁₂ f₀₂ i) (h₁₃ : MulStruct f₁₂ f₂₃ f₁₃ i)
    (h : MulStruct f₀₂ f₂₃ f₀₃ i) :
    MulStruct f₀₁ f₁₃ f₀₃ i :=
  sorry

section

variable {p q r : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}

noncomputable def mulOneEqSymm (h : MulStruct p .const q i) :
    MulStruct q .const p i :=
  assoc h (mulOne _ i) (mulOne p i)

noncomputable def oneMulEqSymm (h : MulStruct .const p q i) :
    MulStruct .const q p i :=
  assoc' (oneMul _ i) h (oneMul p i)

noncomputable def oneMulEqOfMulOneEq (h : MulStruct p .const q i) :
    MulStruct .const p q i :=
  (assoc' (oneMul p i) h (mulOne p i)).oneMulEqSymm

noncomputable def mulOneEqOfOneMulEq (h : MulStruct .const p q i) :
    MulStruct p .const q i :=
  (assoc h (mulOne p i) (oneMul p i)).mulOneEqSymm

noncomputable def mulOneEqTrans (h : MulStruct p .const q i)
    (h' : MulStruct q .const r i) :
    MulStruct p .const r i :=
  assoc (oneMul p i) h h'.oneMulEqOfMulOneEq

noncomputable def oneMulEqTrans (h : MulStruct .const p q i)
    (h' : MulStruct .const q r i) :
    MulStruct .const p r i :=
  assoc' h (mulOne p i) h'.mulOneEqOfOneMulEq

end

end MulStruct

namespace RelStruct

variable [IsFibrant X]

open MulStruct

noncomputable def symm {p q : X.PtSimplex n x} {i : Fin (n + 1)} (h : RelStruct p q i) :
    RelStruct q p i := by
  obtain _ | n  := n
  · obtain rfl : i = 0 := by fin_cases i; rfl
    exact RelStruct₀.equiv₀.symm ((RelStruct₀.equiv₀ h).inv)
  · apply Nonempty.some
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · exact ⟨relStructCastSuccEquivMulStruct.symm
        (oneMulEqSymm ((relStructCastSuccEquivMulStruct (i := 0) h)))⟩
    · exact ⟨relStructSuccEquivMulStruct.symm
        (mulOneEqSymm (relStructSuccEquivMulStruct h))⟩

noncomputable def trans {p q r : X.PtSimplex n x} {i : Fin (n + 1)} (h : RelStruct p q i)
    (h' : RelStruct q r i) : RelStruct p r i := by
  obtain _ | n := n
  · obtain rfl : i = 0 := by fin_cases i; rfl
    exact RelStruct₀.equiv₀.symm ((RelStruct₀.equiv₀ h').comp (RelStruct₀.equiv₀ h))
  · apply Nonempty.some
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · exact ⟨relStructCastSuccEquivMulStruct.symm
        (oneMulEqTrans
        ((relStructCastSuccEquivMulStruct (i := 0) h))
        ((relStructCastSuccEquivMulStruct (i := 0) h')))⟩
    · exact ⟨relStructSuccEquivMulStruct.symm
        (mulOneEqTrans (relStructSuccEquivMulStruct h')
        (relStructSuccEquivMulStruct h))⟩

noncomputable def succ {p q : X.PtSimplex n x} {i : Fin n} (h : RelStruct p q i.castSucc) :
    RelStruct p q i.succ := by
  obtain _ | n := n
  · exfalso
    fin_cases i
  · exact relStructSuccEquivMulStruct.symm
      (mulOneEqOfOneMulEq (relStructCastSuccEquivMulStruct h.symm))

noncomputable def ofSucc {p q : X.PtSimplex n x} {i : Fin n} (h : RelStruct p q i.succ) :
    RelStruct p q i.castSucc := by
  obtain _ | n := n
  · exfalso
    fin_cases i
  · exact relStructCastSuccEquivMulStruct.symm
      ((oneMulEqOfMulOneEq (relStructSuccEquivMulStruct h.symm)))

noncomputable def relStruct₀ {p q : X.PtSimplex n x} {i : Fin (n + 1)} (h : RelStruct p q i) :
    RelStruct₀ p q := by
  induction i using Fin.induction  with
  | zero => exact h
  | succ i hi => exact hi h.ofSucc

end RelStruct

namespace RelStruct₀

variable [IsFibrant X]

noncomputable def relStruct {p q : X.PtSimplex n x}
    (h : RelStruct₀ p q) (i : Fin (n + 1)) : RelStruct p q i := by
  obtain _ | n := n
  · obtain rfl : i = 0 := by aesop
    exact h
  · induction i using Fin.induction  with
    | zero => exact h
    | succ i hi => exact hi.succ

def refl (p : X.PtSimplex n x) : RelStruct₀ p p := RelStruct.refl _ _

noncomputable def symm {p q : X.PtSimplex n x} (h : RelStruct₀ p q) : RelStruct₀ q p :=
  RelStruct.symm h

noncomputable def trans {p q r : X.PtSimplex n x} (h : RelStruct₀ p q) (h' : RelStruct₀ q r) :
    RelStruct₀ p r :=
  RelStruct.trans h h'

end RelStruct₀

namespace MulStruct

variable [IsFibrant X] {i : Fin (n + 1)}

noncomputable def unique {p₀₁ p₁₂ p₀₂ p₀₁' p₁₂' p₀₂' : X.PtSimplex (n + 1) x}
    (h : MulStruct p₀₁ p₁₂ p₀₂ i)
    (h' : MulStruct p₀₁' p₁₂' p₀₂' i)
    (h₀₁ : RelStruct₀ p₀₁ p₀₁') (h₁₂ : RelStruct₀ p₁₂ p₁₂') :
    RelStruct₀ p₀₂ p₀₂' :=
  RelStruct.relStruct₀
    (relStructSuccEquivMulStruct.symm
      (assoc h' (relStructSuccEquivMulStruct (h₁₂.relStruct i.succ))
        (assoc (relStructSuccEquivMulStruct (h₀₁.symm.relStruct i.succ)) (oneMul p₁₂ i) h)))

noncomputable def unique' {p₀₁ p₁₂ p₀₂ p₀₂' : X.PtSimplex (n + 1) x}
    (h : MulStruct p₀₁ p₁₂ p₀₂ i) (h₀₂ : RelStruct₀ p₀₂ p₀₂') :
    MulStruct p₀₁ p₁₂ p₀₂' i :=
  MulStruct.assoc' h (mulOne p₁₂ i)
    (relStructSuccEquivMulStruct (h₀₂.symm.relStruct i.succ))

variable (p q) in
lemma nonempty (i : Fin (n + 1)) :
    ∃ (r : X.PtSimplex (n + 1) x), Nonempty (MulStruct p q r i) := by
  let α (j : ({i.succ.castSucc}ᶜ : Set (Fin (n + 3)))) : X.PtSimplex (n + 1) x :=
    if j = i.castSucc.castSucc then q else
      if j = i.succ.succ then p else
        .const
  have hα₀ (j) (hj : j.1 < i.castSucc.castSucc) : α j = .const := by
    dsimp [α]
    rw [if_neg, if_neg]
    all_goals
      simp [Fin.ext_iff, Fin.lt_iff_val_lt_val] at hj ⊢
      omega
  have hα₁ : α ⟨i.castSucc.castSucc, by simp [Fin.ext_iff]⟩ = q := if_pos rfl
  have hα₂ : α ⟨i.succ.succ, by simp [Fin.ext_iff]⟩ = p := by
    dsimp [α]
    rw [if_neg, if_pos rfl]
    simp [Fin.ext_iff]
    omega
  have hα₃ (j) (hj : i.succ.succ < j.1) : α j = .const := by
    dsimp [α]
    rw [if_neg, if_neg]
    all_goals
      simp [Fin.ext_iff, Fin.lt_iff_val_lt_val] at hj ⊢
      omega
  obtain ⟨β, hβ⟩ := subcomplexHorn.exists_desc (fun j ↦ (α j).map) (by simp)
  obtain ⟨γ, hγ⟩ := anodyneExtensions.exists_lift_of_isFibrant β
    (anodyneExtensions.subcomplexHorn_ι_mem _ _)
  replace hγ (j : Fin (n + 3)) (hj : j ≠ i.succ.castSucc) :
      standardSimplex.map (SimplexCategory.δ j) ≫ γ = (α ⟨j, hj⟩).map := by
    rw [← hβ, ← hγ, subcomplexHorn.ι_ι_assoc]
  refine ⟨.mk (standardSimplex.map (SimplexCategory.δ i.succ.castSucc) ≫ γ) ?_, ⟨?_⟩⟩
  · intro j
    rw [← Functor.map_comp_assoc, ← Fin.succ_castSucc]
    by_cases hj : j ≤ i.castSucc
    · rw [SimplexCategory.δ_comp_δ hj, Functor.map_comp_assoc,
        hγ, δ_map]
      simp [Fin.ext_iff, Fin.le_iff_val_le_val] at hj ⊢
      omega
    · rw [Fin.succ_castSucc, ← SimplexCategory.δ_comp_δ (by simpa using hj),
        Functor.map_comp_assoc, hγ, δ_map]
      simp [Fin.ext_iff, Fin.le_iff_val_le_val] at hj ⊢
      omega
  · exact {
      map := γ
      δ_succ_succ_map := by rw [hγ, hα₂]
      δ_castSucc_castSucc_map := by rw [hγ, hα₁]
      δ_castSucc_succ_map := rfl
      δ_map_of_lt j hj := by
        rw [hγ, hα₀ _ hj, Subcomplex.RelativeMorphism.const_map]
        rintro rfl
        simp [Fin.lt_iff_val_lt_val] at hj
      δ_map_of_gt j hj := by
        rw [hγ, hα₃ _ hj, Subcomplex.RelativeMorphism.const_map]
        rintro rfl
        simp [Fin.lt_iff_val_lt_val] at hj
    }

-- this should be similar to `nonempty` above
variable (p) in
lemma exists_left_inverse (i : Fin (n + 1)) :
    ∃ (q : X.PtSimplex (n + 1) x), Nonempty (MulStruct q p .const i) := by
  sorry

end MulStruct

variable [IsFibrant X] (p q : X.PtSimplex n x)

abbrev Homotopy := Subcomplex.RelativeMorphism.Homotopy p q

variable {p q}

noncomputable def Homotopy.relStruct₀ (h : p.Homotopy q) : RelStruct₀ p q := sorry

noncomputable def RelStruct₀.homotopy (h : RelStruct₀ p q) : p.Homotopy q := sorry

noncomputable def RelStruct.homotopy {i : Fin (n + 1)} (h : RelStruct p q i) : p.Homotopy q :=
  h.relStruct₀.homotopy

end PtSimplex

end SSet
