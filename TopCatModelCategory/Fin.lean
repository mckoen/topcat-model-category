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

lemma orderHom_injective_iff {α : Type*} [PartialOrder α] {n : ℕ} (f : Fin (n + 1) →o α) :
    Function.Injective f ↔ ∀ (i : Fin n), f i.castSucc ≠ f i.succ := by
  constructor
  · intro hf i h
    simpa [Fin.ext_iff] using hf h
  · intro hf i j h
    wlog hij : i ≤ j generalizing i j h
    · exact (this h.symm (by omega)).symm
    obtain ⟨k, hk⟩ := Nat.le.dest hij
    cases k with
    | zero => ext; omega
    | succ k =>
        let l : Fin n := ⟨i.1, by omega⟩
        have h₁ : f i < f l.succ := by
          rw [lt_iff_le_and_ne]
          exact ⟨f.monotone l.castSucc_le_succ, hf l⟩
        have h₂ : f i < f j := lt_of_lt_of_le h₁ (f.monotone (by
          simp only [Fin.le_def, val_succ]
          omega))
        exact (h₂.ne h).elim

@[simps]
def oneOrderHomEquiv {α : Type*} [Preorder α] :
    (Fin 1 →o α) ≃ α where
  toFun f := f 0
  invFun a :=
    { toFun _ := a
      monotone' _ _ _ := by aesop }
  left_inv _ := by
    ext i
    obtain rfl := Subsingleton.elim 0 i
    rfl
  right_inv _ := rfl

end Fin
