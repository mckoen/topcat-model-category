import TopCatModelCategory.SSet.Degenerate

open CategoryTheory Simplicial MonoidalCategory

universe u

namespace Fin

def orderHom_injective_iff {α : Type*} [PartialOrder α] {n : ℕ} (f : Fin (n + 1) →o α) :
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
        have pif := hf l
        have h₁ : f i < f l.succ := by
          rw [lt_iff_le_and_ne]
          exact ⟨f.monotone l.castSucc_le_succ, hf l⟩
        have h₂ : f i < f j := lt_of_lt_of_le h₁ (f.monotone (by
          simp only [Fin.le_def, val_succ]
          omega))
        exact (h₂.ne h).elim

end Fin

namespace SSet

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

lemma objEquiv_non_degenerate_iff (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) :
    z ∈ (Δ[p] ⊗ Δ[q]).NonDegenerate n ↔ Function.Injective (objEquiv z) := by
  sorry

end prodStandardSimplex

end SSet
