import Mathlib.Algebra.Group.Nat.Basic
import Mathlib.Order.Fin.Basic

namespace Fin

lemma monotone_iff {α : Type u} [Preorder α] {n : ℕ} (f : Fin (n + 1) → α) :
    Monotone f ↔ ∀ (i : Fin n), f i.castSucc ≤ f i.succ := by
  refine ⟨fun hf i ↦ hf i.castSucc_le_succ, fun hf ↦ ?_⟩
  let P (k : ℕ) := ∀ (i : ℕ) (hi : i + k ≤ n), f ⟨i, by omega⟩ ≤ f ⟨i + k, by omega⟩
  suffices ∀ k, P k by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (h : i ≤ j)
    obtain ⟨k, rfl⟩ := Nat.le.dest h
    exact this k i (by omega)
  intro k
  induction k with
  | zero => simp [P]
  | succ k hk =>
      intro i hi
      simp only [← add_assoc]
      exact (hk i (by omega)).trans (hf ⟨i + k, by omega⟩)

end Fin
