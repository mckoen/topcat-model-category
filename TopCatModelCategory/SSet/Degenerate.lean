import Mathlib.AlgebraicTopology.SimplicialSet.Basic

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

variable (X : SSet.{u})

def Degenerate (n : ℕ) : Set (X _[n]) :=
  setOf (fun x ↦ ∃ (m : SimplexCategory) (_ : m.len < n) (f : ([n] : SimplexCategory) ⟶ m),
    x ∈ Set.range (X.map f.op))

def NonDegenerate (n : ℕ) : Set (X _[n]) := (X.Degenerate n)ᶜ

@[simp]
lemma degenerate_zero : X.Degenerate 0 = ⊥ := by
  ext x
  simp only [Set.bot_eq_empty, Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, hm, _⟩
  simp at hm

@[simp]
lemma nondegenerate_zero : X.NonDegenerate 0 = ⊤ := by
  simp [NonDegenerate]

variable {n : ℕ}

lemma mem_nondegenerate_iff_not_mem_degenerate (x : X _[n]) :
    x ∈ X.NonDegenerate n ↔ x ∉ X.Degenerate n := Iff.rfl

lemma mem_degenerate_iff_non_mem_nondegenerate (x : X _[n]) :
    x ∈ X.Degenerate n ↔ x ∉ X.NonDegenerate n := by
  simp [NonDegenerate]

lemma σ_mem_degenerate (i : Fin (n + 1)) (x : X _[n]) :
    X.σ i x ∈ X.Degenerate (n + 1) :=
  ⟨[n], by dsimp; omega, SimplexCategory.σ i, Set.mem_range_self x⟩

lemma mem_degenerate_iff (x : X _[n]) :
    x ∈ X.Degenerate n ↔ ∃ (m : ℕ) (_ : m < n)
      (f : ([n] : SimplexCategory) ⟶ [m]) (_ : Epi f),
        x ∈ Set.range (X.map f.op) := by
  trans ∃ (m : SimplexCategory) (_ : m.len < n)
      (f : ([n] : SimplexCategory) ⟶ m) (_ : Epi f),
        x ∈ Set.range (X.map f.op)
  · constructor
    · rintro ⟨m, hm, f, hf, hx⟩
      rw [← image.fac f, op_comp] at hx
      have := SimplexCategory.len_le_of_mono (f := image.ι f) inferInstance
      exact ⟨_, by omega, factorThruImage f, inferInstance, by aesop⟩
    · rintro ⟨m, hm, f, hf, hx⟩
      exact ⟨m, hm, f, hx⟩
  · constructor
    · rintro ⟨m, hm, f, hf, hx⟩
      exact ⟨m.len, hm, f, hf, hx⟩
    · rintro ⟨m, hm, f, hf, hx⟩
      exact ⟨[m], hm, f, hf, hx⟩

lemma degenerate_eq_iUnion_range_σ :
    X.Degenerate (n + 1) = ⨆ (i : Fin (n + 1)), Set.range (X.σ i) := by
  ext x
  constructor
  · intro hx
    rw [mem_degenerate_iff] at hx
    obtain ⟨m, hm, f, hf, y, rfl⟩ := hx
    obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f (fun hf ↦ by
      have := SimplexCategory.le_of_mono (f := f) (by
        rwa [SimplexCategory.mono_iff_injective])
      omega)
    aesop
  · intro hx
    simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, y, rfl⟩ := hx
    apply σ_mem_degenerate

lemma exists_non_degenerate (x : X _[n]) :
    ∃ (m : ℕ) (f : ([n] : SimplexCategory) ⟶ [m]) (_ : Epi f)
      (y : X.NonDegenerate m), x = X.map f.op y := by
  revert x
  induction n with
  | zero =>
      intro x
      exact ⟨0, 𝟙 _, inferInstance, ⟨x, by simp⟩, by simp⟩
  | succ n hn =>
      intro x
      by_cases hx : x ∈ X.NonDegenerate (n + 1)
      · exact ⟨n + 1, 𝟙 _, inferInstance, ⟨x, hx⟩, by simp⟩
      · simp only [← mem_degenerate_iff_non_mem_nondegenerate,
          degenerate_eq_iUnion_range_σ, Set.iSup_eq_iUnion,
          Set.mem_iUnion, Set.mem_range] at hx
        obtain ⟨i, y, rfl⟩ := hx
        obtain ⟨m, f, hf, z, rfl⟩ := hn y
        exact ⟨_, SimplexCategory.σ i ≫ f, inferInstance, z, by simp; rfl⟩

lemma isIso_of_non_degenerate (x : X.NonDegenerate n)
    {m : SimplexCategory} (f : ([n] : SimplexCategory) ⟶ m) [Epi f]
    (y : X.obj (op m)) (hy : X.map f.op y = x) :
    IsIso f := by
  obtain ⟨x, hx⟩ := x
  induction' m using SimplexCategory.rec with m
  rw [mem_nondegenerate_iff_not_mem_degenerate] at hx
  by_contra!
  refine hx ⟨_ ,?_, f, y, hy⟩
  by_contra!
  obtain rfl : m = n :=
    le_antisymm (SimplexCategory.len_le_of_epi (f := f) inferInstance) this
  obtain rfl := SimplexCategory.eq_id_of_epi f
  exact this inferInstance

lemma unique_dimension_non_degenerate_aux (x : X _[n])
    {m₁ m₂ : ℕ} (f₁ : ([n] : SimplexCategory) ⟶ [m₁]) [Epi f₁]
    (y₁ : X.NonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ([n] : SimplexCategory) ⟶ [m₂]) [Epi f₂]
    (y₂ : X _[m₂]) (hy₂ : x = X.map f₂.op y₂) : m₁ ≤ m₂ := by
  have := isSplitEpi_of_epi f₁
  let g := section_ f₁ ≫ f₂
  have h : X.map g.op y₂ = y₁ := by
    dsimp [g]
    rw [FunctorToTypes.map_comp_apply, ← hy₂, hy₁, ← FunctorToTypes.map_comp_apply, ← op_comp,
      IsSplitEpi.id, op_id, FunctorToTypes.map_id_apply]
  rw [← image.fac g, op_comp, FunctorToTypes.map_comp_apply] at h
  have := X.isIso_of_non_degenerate y₁ (factorThruImage g) _ h
  exact SimplexCategory.len_le_of_mono (f := factorThruImage g ≫ image.ι g) inferInstance

lemma unique_non_degenerate₁ (x : X _[n])
    {m₁ m₂ : ℕ} (f₁ : ([n] : SimplexCategory) ⟶ [m₁]) [Epi f₁]
    (y₁ : X.NonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ([n] : SimplexCategory) ⟶ [m₂]) [Epi f₂]
    (y₂ : X.NonDegenerate m₂) (hy₂ : x = X.map f₂.op y₂) : m₁ = m₂ :=
  le_antisymm (X.unique_dimension_non_degenerate_aux x f₁ y₁ hy₁ f₂ y₂ hy₂)
    (X.unique_dimension_non_degenerate_aux x f₂ y₂ hy₂ f₁ y₁ hy₁)

lemma unique_non_degenerate₂ (x : X _[n])
    {m : ℕ} (f₁ : ([n] : SimplexCategory) ⟶ [m]) [Epi f₁]
    (y₁ : X.NonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ([n] : SimplexCategory) ⟶ [m]) [Epi f₂]
    (y₂ : X.NonDegenerate m) (hy₂ : x = X.map f₂.op y₂) : y₁ = y₂ := sorry

lemma unique_non_degenerate₃ (x : X _[n])
    {m : ℕ} (f₁ : ([n] : SimplexCategory) ⟶ [m]) [Epi f₁]
    (f₂ : ([n] : SimplexCategory) ⟶ [m]) [Epi f₂]
    (y : X.NonDegenerate m) (hy₁ : x = X.map f₁.op y)
    (hy₂ : x = X.map f₂.op y) : f₁ = f₂ := sorry


end SSet
