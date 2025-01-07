import TopCatModelCategory.SSet.StandardSimplex

universe u

open Simplicial

namespace SSet

variable (X : SSet.{u})

class IsFinite : Prop where
  finite : Finite (Σ (n : ℕ), X.NonDegenerate n)

attribute [instance] IsFinite.finite

lemma isFinite_of_hasDimensionLT (d : ℕ) [X.HasDimensionLT d]
    (h : ∀ (i : ℕ) (_ : i < d), Finite (X.NonDegenerate i)) :
    X.IsFinite where
  finite := by
    have (i : Fin d) : Finite (X.NonDegenerate i) := h i.1 i.2
    apply Finite.of_surjective (α := Σ (i : Fin d), X.NonDegenerate i)
      (f := fun ⟨i, x⟩ ↦ ⟨i.1, x⟩)
    rintro ⟨j, ⟨x, hx⟩⟩
    by_cases hj : j < d
    · exact ⟨⟨⟨j, hj⟩, ⟨x, hx⟩⟩, rfl⟩
    · simp [X.nondegenerate_eq_bot_of_hasDimensionLT d j (by simpa using hj)] at hx

instance (n : ℕ) : (Δ[n] : SSet.{u}).IsFinite :=
  isFinite_of_hasDimensionLT _ (n + 1) (by infer_instance)

lemma hasDimensionLT_of_isFinite [X.IsFinite] :
    ∃ (d : ℕ), X.HasDimensionLT d := by
  have : Fintype (Σ (n : ℕ), X.NonDegenerate n) := Fintype.ofFinite _
  let φ : (Σ (n : ℕ), X.NonDegenerate n) → ℕ := Sigma.fst
  obtain ⟨d, hd⟩ : ∃ (d : ℕ), ∀ (s : ℕ) (_ : s ∈ Finset.image φ ⊤), s < d := by
    by_cases h : (Finset.image φ ⊤).Nonempty
    · obtain ⟨d, hd⟩ := Finset.max_of_nonempty h
      refine ⟨d + 1, ?_⟩
      rintro m hm
      have := Finset.le_max hm
      rw [hd, WithBot.coe_le_coe] at this
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      simp only [h]
      exact ⟨0, fun s hs ↦ by simp at hs⟩
  refine ⟨d, ⟨fun n hn ↦ ?_⟩⟩
  ext x
  simp only [mem_degenerate_iff_non_mem_nondegenerate, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  intro hx
  have := hd (φ ⟨n, ⟨x, hx⟩⟩) (by simp)
  dsimp [φ] at this
  omega

end SSet
