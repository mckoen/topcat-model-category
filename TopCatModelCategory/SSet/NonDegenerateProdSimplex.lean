import TopCatModelCategory.SSet.Degenerate
import TopCatModelCategory.SSet.StandardSimplex
import TopCatModelCategory.Fin

open CategoryTheory Simplicial MonoidalCategory Opposite

universe u

namespace SSet

def standardSimplex.objMk₁ {n : ℕ} (i : Fin (n + 2)) : Δ[1] _[n] :=
  objMk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        by_cases hi : j₁.castSucc < i
        · simp [if_pos hi]
        · rw [if_neg hi, if_neg (fun hj' ↦ hi (lt_of_le_of_lt (by simpa using h) hj'))] }

namespace prodStandardSimplex

variable {p q : ℕ}

def objEquiv {n : ℕ} :
    (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n] ≃ (Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)) where
  toFun := fun ⟨x, y⟩ ↦ OrderHom.prod
      ((standardSimplex.objEquiv _ _ x).toOrderHom)
      ((standardSimplex.objEquiv _ _ y).toOrderHom)
  invFun f :=
    ⟨(standardSimplex.objEquiv _ _ ).symm
      (SimplexCategory.Hom.mk (OrderHom.fst.comp f)),
      (standardSimplex.objEquiv _ _ ).symm
      (SimplexCategory.Hom.mk (OrderHom.snd.comp f))⟩
  left_inv := fun ⟨x, y⟩ ↦ by simp
  right_inv _ := rfl

lemma objEquiv_naturality {m n : ℕ} (f : ([m] : SimplexCategory) ⟶ [n])
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) :
    (objEquiv z).comp f.toOrderHom = objEquiv ((Δ[p] ⊗ Δ[q]).map f.op z) :=
  rfl

def obj₀Equiv : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[0] ≃ Fin (p + 1) × Fin (q + 1) :=
  objEquiv.trans Fin.oneOrderHomEquiv

noncomputable abbrev subsimplex {n : ℕ} (f : Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)) :
    (Δ[p] ⊗ Δ[q] : SSet.{u}).Subcomplex :=
  Subcomplex.ofSimplex (objEquiv.symm f)

lemma subsimplex_obj_zero {n : ℕ} (f : Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)) :
    (subsimplex f).obj (op [0]) =
      Set.image (obj₀Equiv.{u}).symm (Set.range f) := by
  ext x
  simp [subsimplex]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, rfl⟩ := standardSimplex.obj₀Equiv.symm.surjective x
    exact ⟨i, rfl⟩
  · rintro ⟨i, hx⟩
    exact ⟨standardSimplex.obj₀Equiv.symm i, obj₀Equiv.injective (by rw [← hx]; rfl)⟩

lemma mem_subsimplex_iff {n : ℕ} (f : Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)) {m : ℕ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[m]) :
    x ∈ (subsimplex f).obj _ ↔ Set.range (objEquiv x) ⊆ Set.range f := by
  constructor
  · rintro ⟨x, rfl⟩ _ ⟨i, rfl⟩
    obtain ⟨g, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective x
    exact ⟨g.toOrderHom i, rfl⟩
  · intro hf
    let S (i : Fin (m + 1)) : Finset (Fin (n + 1)) := { j | f j = objEquiv x i }
    have hS (i : Fin (m + 1)) : (S i).Nonempty := by
      obtain ⟨j, hj⟩ := hf (Set.mem_range_self i)
      exact ⟨j, by simpa [S] using hj⟩
    let φ (i : Fin (m + 1)) : Fin (n + 1) := (S i).min' (hS i)
    have hφ (i : Fin (m + 1)) : f (φ i) = objEquiv x i := by
      simpa [S] using (S i).min'_mem (hS i)
    refine ⟨standardSimplex.objMk { toFun := φ, monotone' := ?_ }, ?_⟩
    · intro i₁ i₂ h₁
      obtain h₂ | h₂ := ((objEquiv x).monotone h₁).lt_or_eq
      · simp only [← hφ] at h₂
        by_contra! h₃
        have h₄ := lt_of_lt_of_le h₂ (f.monotone h₃.le)
        simp at h₄
      · simp [φ, S, h₂]
    · apply objEquiv.injective
      ext i : 2
      rw [← hφ]
      rfl

lemma subsimplex_le_subsimplex_iff {n m : ℕ}
    (f : Fin (n + 1) →o Fin (p + 1) × Fin (q + 1))
    (g : Fin (m + 1) →o Fin (p + 1) × Fin (q + 1)) :
    subsimplex.{u} f ≤ subsimplex.{u} g ↔
      Set.range f ⊆ Set.range g := by
  constructor
  · intro h
    simpa [subsimplex_obj_zero] using h (op [0])
  · rintro h ⟨k⟩ x
    induction' k using SimplexCategory.rec with k
    simp only [mem_subsimplex_iff]
    intro h'
    exact h'.trans h

lemma objEquiv_non_degenerate_iff (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) :
    z ∈ (Δ[p] ⊗ Δ[q]).NonDegenerate n ↔ Function.Injective (objEquiv z) := by
  rw [Fin.orderHom_injective_iff, ← not_iff_not,
    ← mem_degenerate_iff_non_mem_nondegenerate]
  simp only [not_forall, ne_eq, Decidable.not_not]
  obtain _ | n := n
  · simp
  · simp only [degenerate_eq_iUnion_range_σ, Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_range]
    apply exists_congr
    intro i
    constructor
    · rintro ⟨x, rfl⟩
      simp [SimplicialObject.σ, ← objEquiv_naturality, SimplexCategory.σ]
    · intro h₁
      refine ⟨SimplicialObject.δ (Δ[p] ⊗ Δ[q] : SSet.{u}) i.castSucc z, ?_⟩
      apply objEquiv.injective
      ext j : 2
      dsimp [SimplicialObject.σ, SimplicialObject.δ,
        SimplexCategory.σ, SimplexCategory.δ]
      rw [← objEquiv_naturality, ← objEquiv_naturality]
      dsimp
      by_cases h₂ : j = i.castSucc
      · simpa [h₂] using h₁.symm
      · rw [Fin.succAbove_predAbove h₂]

noncomputable def nonDegenerateEquiv₁ :
    Fin (q + 1) ≃ (Δ[1] ⊗ Δ[q]).NonDegenerate (q + 1) :=
  Equiv.ofBijective (fun i ↦ ⟨⟨standardSimplex.objMk₁ i.succ.castSucc,
    (standardSimplex.objEquiv _ _).symm (SimplexCategory.σ i)⟩, by
      rw [objEquiv_non_degenerate_iff, Fin.orderHom_injective_iff]
      intro j h
      have h₁ := congr_arg Prod.fst h
      have h₂ := congr_arg Prod.snd h
      have h₂' := congr_arg Fin.val h₂
      simp [objEquiv, standardSimplex.objMk₁, SimplexCategory.σ] at h₁ h₂ h₂'
      by_cases h₃ : j ≤ i
      · rw [Fin.predAbove_of_le_castSucc _ _  h₃] at h₂'
        obtain h₃ | rfl := h₃.lt_or_eq
        · rw [Fin.predAbove_of_le_castSucc] at h₂'; swap
          · rw [Fin.lt_iff_val_lt_val, Fin.val_fin_lt] at h₃
            rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]
            omega
          · simp [Fin.castPred, Fin.castLT] at h₂'
        · simp at h₁
      · simp at h₃
        rw [Fin.lt_iff_val_lt_val] at h₃
        rw [Fin.predAbove_of_castSucc_lt] at h₂; swap
        · simpa only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc] using h₃
        have := i.predAbove_of_castSucc_lt j.succ (by
          rw [Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ]
          apply h₃.trans (lt_add_one _))
        -- bug in Lean ?? rw [this] at h₂
        sorry⟩) sorry

end prodStandardSimplex

end SSet
