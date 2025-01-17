import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Card

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
          simp only [Fin.le_def, val_succ, l]
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

lemma orderHom_ext_of_injective_aux {α : Type*} [PartialOrder α] [DecidableEq α]
    {n : ℕ} {f g : Fin n →o α}
    (hg : Function.Injective g)
    (h : Finset.image f ⊤ = Finset.image g ⊤) (i : Fin n)
    (h' : ∀ (j : Fin n), j < i → f j = g j) :
    f i ≤ g i := by
  have : g i ∈ Finset.image f ⊤ := by rw [h]; simp
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and] at this
  obtain ⟨j, hj⟩ := this
  rw [← hj]
  apply f.monotone
  by_contra!
  rw [h' j this] at hj
  obtain rfl := hg hj
  simp at this

lemma orderHom_ext_of_injective {α : Type*} [PartialOrder α] [DecidableEq α]
    {n : ℕ} {f g : Fin n →o α}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : Finset.image f ⊤ = Finset.image g ⊤) :
    f = g := by
  let P (i : ℕ) := ∀ (j : ℕ) (hij : j < i) (hj : j < n), f ⟨j, by omega⟩ = g ⟨j, by omega⟩
  suffices ∀ i, P i by ext i; exact this (i.1 + 1) i.1 (by omega) (by omega)
  suffices ∀ i, P i → P (i + 1) by
    intro i
    induction i with
    | zero =>
        intro _ _
        omega
    | succ i hi => exact fun j hij hj ↦ this _ hi j hij hj
  intro i hi j hij hj
  obtain hij | rfl := (Nat.le_of_lt_succ hij).lt_or_eq
  · exact hi j hij hj
  · apply le_antisymm
    · exact orderHom_ext_of_injective_aux hg h _
        (fun k hk ↦ hi k hk (by omega))
    · exact orderHom_ext_of_injective_aux hf h.symm _
        (fun k hk ↦ (hi k hk (by omega)).symm)

@[simp]
lemma range_succAboveOrderEmb {n : ℕ} (i : Fin (n + 1)) :
    Set.range (Fin.succAboveOrderEmb i).toOrderHom = {i}ᶜ := by aesop


end Fin
