import TopCatModelCategory.SSet.StandardSimplex

universe u

open Simplicial

namespace SSet

variable (X : SSet.{u})

class IsFinite : Prop where
  finite : Finite (Σ (n : ℕ), X.NonDegenerate n)

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

end SSet
