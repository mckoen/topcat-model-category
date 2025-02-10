import TopCatModelCategory.SSet.NonDegenerateProdSimplex

open CategoryTheory Simplicial MonoidalCategory Opposite ChosenFiniteProducts

universe u

namespace SSet

namespace prodStandardSimplex₁

variable {n : ℕ}

noncomputable def nonDegenerateEquiv :
    Fin (n + 1) ≃ (Δ[n] ⊗ Δ[1] : SSet.{u}).NonDegenerate (n + 1) :=
  prodStandardSimplex.nonDegenerateEquiv₁.{u}.trans
    (nonDegenerateEquivOfIso (β_ _ _) _)

@[simp]
lemma nonDegenerateEquiv_fst (i : Fin (n + 1)) :
    (nonDegenerateEquiv i).1.1 =
      (standardSimplex.objEquiv [n] (op [n + 1])).symm (SimplexCategory.σ i) := rfl

@[simp]
lemma nonDegenerateEquiv_snd (i : Fin (n + 1)) :
    (nonDegenerateEquiv i).1.2 =
      standardSimplex.objMk₁ i.succ.castSucc := rfl

lemma mem_range_objEquiv_nonDegenerateEquiv₀_iff (i x : Fin (n + 1)) :
    (x, 0) ∈ Set.range (prodStandardSimplex.objEquiv (nonDegenerateEquiv i).1) ↔ x ≤ i := by
  constructor
  · rintro ⟨y, hy⟩
    have hy₁ := congr_arg Prod.fst hy
    have hy₂ := congr_arg Prod.snd hy
    dsimp at hy₁ hy₂
    rw [standardSimplex.objMk₁_apply_eq_zero_iff, Fin.castSucc_lt_castSucc_iff] at hy₂
    rw [← hy₁, standardSimplex.objEquiv_symm_σ_apply,
      Fin.predAbove_of_lt_succ _ _ hy₂, ← Fin.castSucc_le_castSucc_iff,
      Fin.castSucc_castPred, Fin.le_castSucc_iff]
    exact hy₂
  · intro hx
    refine ⟨x.castSucc, Prod.ext ?_ ?_⟩
    · dsimp
      rw [standardSimplex.objEquiv_symm_σ_apply,
        Fin.predAbove_of_le_castSucc _ _ (by simpa),
        Fin.castPred_castSucc]
    · simpa [standardSimplex.objMk₁_apply_eq_zero_iff]

lemma mem_range_objEquiv_nonDegenerateEquiv₁_iff (i x : Fin (n + 1)) :
    (x, 1) ∈ Set.range (prodStandardSimplex.objEquiv (nonDegenerateEquiv i).1) ↔ i ≤ x := by
  constructor
  · rintro ⟨y, hy⟩
    have hy₁ := congr_arg Prod.fst hy
    have hy₂ := congr_arg Prod.snd hy
    dsimp at hy₁ hy₂
    rw [standardSimplex.objMk₁_apply_eq_one_iff, Fin.castSucc_le_castSucc_iff] at hy₂
    rw [← hy₁, standardSimplex.objEquiv_symm_σ_apply, Fin.predAbove_of_succ_le _ _ hy₂,
      ← Fin.succ_le_succ_iff, Fin.succ_pred]
    exact hy₂
  · intro hx
    refine ⟨x.succ, Prod.ext ?_ ?_⟩
    · dsimp
      rw [standardSimplex.objEquiv_symm_σ_apply,
        Fin.predAbove_of_succ_le _ _ (by simpa), Fin.pred_succ]
    · simpa [standardSimplex.objMk₁_apply_eq_one_iff]

noncomputable def filtration (j : Fin (n + 1)) : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  ⨆ (i : ({i // i ≤ j} : Type)), .ofSimplex (nonDegenerateEquiv i.1).1

lemma ofSimplex_le_filtration {i j : Fin (n + 1)} (hij : i ≤ j) :
    .ofSimplex (nonDegenerateEquiv i).1 ≤ filtration.{u} j :=
  le_iSup (fun (i : {i // i ≤ j}) ↦
    Subcomplex.ofSimplex (nonDegenerateEquiv i.1).1) ⟨i, hij⟩

variable (n) in
lemma filtration_zero :
    filtration.{u} (0 : Fin (n + 1)) = .ofSimplex (nonDegenerateEquiv 0).1 :=
  le_antisymm (by simp [filtration]) (ofSimplex_le_filtration.{u} (by rfl))

noncomputable def intersectionNondeg (i j : Fin (n + 1)) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  .ofSimplex (nonDegenerateEquiv i).1 ⊓ .ofSimplex (nonDegenerateEquiv j).1

@[simps coe_fst coe_snd]
def codimOneSimplex (j : Fin (n + 2)) : (Δ[n] ⊗ Δ[1] : SSet.{u}).NonDegenerate n :=
  ⟨⟨standardSimplex.objMk .id, standardSimplex.objMk₁ j⟩, by
    have := standardSimplex.id_nonDegenerate.{u} n
    rw [mem_nondegenerate_iff_not_mem_degenerate] at this ⊢
    intro h
    exact this (degenerate_map h (fst _ _))⟩

lemma δ_castSucc_nonDegenerateEquiv (j : Fin (n + 1)) :
    (Δ[n] ⊗ Δ[1]).δ j.castSucc (nonDegenerateEquiv j).1 =
      (codimOneSimplex j.castSucc).1 := by
  apply Prod.ext
  · exact (standardSimplex.objEquiv _ _).injective SimplexCategory.δ_comp_σ_self
  · dsimp
    rw [standardSimplex.δ_objMk₁_of_lt _ _ (by simp), Fin.pred_castSucc_succ]

lemma δ_succ_nonDegenerateEquiv (j : Fin (n + 1)) :
    (Δ[n] ⊗ Δ[1]).δ j.succ (nonDegenerateEquiv j).1 =
      (codimOneSimplex j.succ).1 := by
  apply Prod.ext
  · exact (standardSimplex.objEquiv _ _).injective SimplexCategory.δ_comp_σ_succ
  · dsimp
    rw [standardSimplex.δ_objMk₁_of_le _ _ (by simp), Fin.castPred_castSucc]

lemma ofSimplex_codimOneSimplex (j : Fin n) :
    Subcomplex.ofSimplex (codimOneSimplex.{u} j.succ.castSucc).1 =
      intersectionNondeg j.castSucc j.succ := by
  apply le_antisymm
  · dsimp [intersectionNondeg]
    simp only [le_inf_iff, Subcomplex.ofSimplex_le_iff,
      standardSimplex.mem_ofSimplex_obj_iff]
    constructor
    · refine ⟨SimplexCategory.δ j.succ.castSucc, ?_⟩
      rw [← Fin.succ_castSucc, ← δ_succ_nonDegenerateEquiv]
      rfl
    · refine ⟨SimplexCategory.δ j.succ.castSucc, ?_⟩
      rw [← δ_castSucc_nonDegenerateEquiv]
      rfl
  · rintro ⟨k⟩ s hs
    induction' k using SimplexCategory.rec with k
    obtain ⟨f, rfl⟩ := prodStandardSimplex.objEquiv.symm.surjective s
    simp only [prodStandardSimplex.mem_ofSimplex_iff, intersectionNondeg,
      Subpresheaf.min_obj, Set.mem_inter_iff, Equiv.apply_symm_apply] at hs ⊢
    rintro ⟨x, y⟩ hxy
    refine ⟨x, Prod.ext rfl ?_⟩
    obtain ⟨x₁, h₁⟩ := hs.1 hxy
    obtain ⟨x₂, h₂⟩ := hs.2 hxy
    have h₁₁ := congr_arg Prod.fst h₁
    have h₁₂ := congr_arg Prod.snd h₁
    have h₂₁ := congr_arg Prod.fst h₂
    have h₂₂ := congr_arg Prod.snd h₂
    simp only [prodStandardSimplex.objEquiv_apply_fst, nonDegenerateEquiv_fst,
      prodStandardSimplex.objEquiv_apply_snd, nonDegenerateEquiv_snd] at h₁₁ h₁₂ h₂₁ h₂₂
    rw [standardSimplex.objEquiv_symm_σ_apply] at h₁₁ h₂₁
    simp only [prodStandardSimplex.objEquiv_apply_snd, codimOneSimplex_coe_snd]
    fin_cases y
    · simp [standardSimplex.objMk₁_apply_eq_zero_iff,
        ← Fin.le_castSucc_iff] at h₁₂ h₂₂ ⊢
      rw [Fin.predAbove_of_le_castSucc _ _ h₁₂] at h₁₁
      simpa [← h₁₁] using h₁₂
    · simp [standardSimplex.objMk₁_apply_eq_one_iff] at h₁₂ h₂₂ ⊢
      rw [Fin.predAbove_of_castSucc_lt _ _ h₂₂] at h₂₁
      rw [← h₂₁, ← Fin.succ_le_succ_iff, Fin.succ_pred]
      exact h₂₂

lemma intersectionNondeg_le_intersectionNondeg (i j k : Fin (n + 1))
    (hij : i ≤ j) (hij : j ≤ k) :
    intersectionNondeg.{u} i k ≤ intersectionNondeg.{u} j k := by
  rintro ⟨k⟩ x hx
  induction' k using SimplexCategory.rec with k
  dsimp [intersectionNondeg] at hx ⊢
  simp only [Set.mem_inter_iff, prodStandardSimplex.mem_ofSimplex_iff,
    ← Set.subset_inter_iff] at hx ⊢
  apply hx.trans
  rintro ⟨x, y⟩ hxy
  simp only [Set.mem_inter_iff] at hxy ⊢
  fin_cases y
  all_goals
  · dsimp at hxy ⊢
    simp only [mem_range_objEquiv_nonDegenerateEquiv₀_iff,
      mem_range_objEquiv_nonDegenerateEquiv₁_iff] at hxy ⊢
    omega

lemma intersectionNondeg_le_intersectionNondeg' (i j k : Fin (n + 1))
    (hij : i ≤ j) (hij : j ≤ k) :
    intersectionNondeg.{u} i k ≤ intersectionNondeg.{u} i j := by
  rintro ⟨k⟩ x hx
  induction' k using SimplexCategory.rec with k
  dsimp [intersectionNondeg] at hx ⊢
  simp only [Set.mem_inter_iff, prodStandardSimplex.mem_ofSimplex_iff,
    ← Set.subset_inter_iff] at hx ⊢
  apply hx.trans
  rintro ⟨x, y⟩ hxy
  simp only [Set.mem_inter_iff] at hxy ⊢
  fin_cases y
  all_goals
  · dsimp at hxy ⊢
    simp only [mem_range_objEquiv_nonDegenerateEquiv₀_iff,
      mem_range_objEquiv_nonDegenerateEquiv₁_iff] at hxy ⊢
    omega

lemma sq (j : Fin n) :
    Subcomplex.Sq (Subcomplex.ofSimplex (codimOneSimplex.{u} j.succ.castSucc).1)
      (filtration.{u} j.castSucc) (.ofSimplex (nonDegenerateEquiv j.succ).1)
      (filtration.{u} j.succ) where
  min_eq := by
    rw [ofSimplex_codimOneSimplex]
    apply le_antisymm
    · dsimp [filtration]
      rw [Subcomplex.iSup_inf, iSup_le_iff, Subtype.forall]
      intro i hi
      exact intersectionNondeg_le_intersectionNondeg _ _ _ hi j.castSucc_le_succ
    · dsimp [intersectionNondeg]
      simp only [le_inf_iff, inf_le_right, and_true]
      exact inf_le_left.trans (ofSimplex_le_filtration (by rfl))
  max_eq := by
    apply le_antisymm
    · rw [filtration, sup_le_iff, iSup_le_iff, Subtype.forall]
      constructor
      · intro i hi
        exact ofSimplex_le_filtration (hi.trans (j.castSucc_le_succ))
      · exact ofSimplex_le_filtration (by rfl)
    · rw [filtration, iSup_le_iff, Subtype.forall]
      intro i hi
      obtain hi | rfl := hi.lt_or_eq
      · refine le_trans ?_ le_sup_left
        exact ofSimplex_le_filtration (Fin.le_castSucc_iff.2 hi)
      · exact le_sup_right

noncomputable def ι (i : Fin (n + 1)) : (Δ[n + 1] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1] :=
  (yonedaEquiv _ _).symm (nonDegenerateEquiv i)

end prodStandardSimplex₁

end SSet
