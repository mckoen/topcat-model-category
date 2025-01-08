import TopCatModelCategory.SSet.Degenerate

universe u

open CategoryTheory

namespace SSet

class HasDimensionLT (X : SSet.{u}) (d : ℕ) : Prop where
  degenerate_eq_top (n : ℕ) (hn : d ≤ n) : X.Degenerate n = ⊤

section

variable (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d] (n : ℕ)

lemma degenerate_eq_top_of_hasDimensionLT (hn : d ≤ n) : X.Degenerate n = ⊤ :=
  HasDimensionLT.degenerate_eq_top n hn

lemma nondegenerate_eq_bot_of_hasDimensionLT (hn : d ≤ n) : X.NonDegenerate n = ⊥ := by
  simp [NonDegenerate, X.degenerate_eq_top_of_hasDimensionLT d n hn]

end

namespace Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

instance (d : ℕ) [X.HasDimensionLT d] : HasDimensionLT A d where
  degenerate_eq_top (n : ℕ) (hd : d ≤ n) := by
    ext x
    simp [A.mem_degenerate_iff, X.degenerate_eq_top_of_hasDimensionLT d n hd]

lemma eq_top_iff_of_hasDimensionLT (d : ℕ) [X.HasDimensionLT d] :
    A = ⊤ ↔ ∀ (i : ℕ) (_ : i < d), X.NonDegenerate i ⊆ A.obj _ := by
  constructor
  · rintro rfl
    simp
  · intro h
    rw [eq_top_iff_contains_nonDegenerate]
    intro i
    by_cases hi : i < d
    · exact h i hi
    · simp [X.nondegenerate_eq_bot_of_hasDimensionLT d i (by simpa using hi)]

end Subcomplex

lemma hasDimensionLT_of_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (d : ℕ)
    [Y.HasDimensionLT d] : X.HasDimensionLT d where
  degenerate_eq_top n hn := by
    ext x
    rw [← degenerate_iff_of_isIso (toRangeSubcomplex f),
      Subcomplex.mem_degenerate_iff, Y.degenerate_eq_top_of_hasDimensionLT d n hn]
    simp

lemma Subcomplex.hasDimensionLT_of_le {X : SSet.{u}} {A B : X.Subcomplex} (h : A ≤ B)
    (d : ℕ) [HasDimensionLT B d] : HasDimensionLT A d := by
  have := mono_homOfLE h
  exact hasDimensionLT_of_mono (Subcomplex.homOfLE h) d

end SSet
