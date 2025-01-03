import Mathlib.AlgebraicTopology.ModelCategory.Basic
import TopCatModelCategory.MorphismProperty

open CategoryTheory Limits

namespace HomotopicalAlgebra

namespace ModelCategory

variable {C : Type*} [Category C]

def copy [cof : CategoryWithCofibrations C]
    [fib : CategoryWithFibrations C] [W : CategoryWithWeakEquivalences C]
    (h : ModelCategory C) (h₁ : cofibrations C = h.categoryWithCofibrations.cofibrations)
    (h₂ : fibrations C = h.categoryWithFibrations.fibrations)
    (h₃ : weakEquivalences C = h.categoryWithWeakEquivalences.weakEquivalences):
    ModelCategory C := by
  have h₄ : trivialCofibrations C = h.categoryWithCofibrations.cofibrations ⊓
      h.categoryWithWeakEquivalences.weakEquivalences := by
    rw [trivialCofibrations, h₁, h₃]
  have h₅ : trivialFibrations C = h.categoryWithFibrations.fibrations ⊓
    h.categoryWithWeakEquivalences.weakEquivalences := by
    rw [trivialFibrations, h₂, h₃]
  exact {
    cm2 := by rw [h₃]; exact h.cm2
    cm3a := by rw [h₃]; exact h.cm3a
    cm3b := by rw [h₂]; exact h.cm3b
    cm3c := by rw [h₁]; exact h.cm3c
    cm4a i p _ _ _ := by
      have : (trivialCofibrations C).rlp = fibrations C := by
        rw [h₄, h₂]
        exact @trivialCofibrations_rlp _ _ h
      exact this.symm.le p (mem_fibrations p) i (mem_trivialCofibrations i)
    cm4b i p _ _ _ := by
      have : (cofibrations C).rlp = trivialFibrations C := by
        rw [h₅, h₁]
        exact @cofibrations_rlp _ _ h
      exact this.symm.le p (mem_trivialFibrations p) i (mem_cofibrations i)
    cm5a := by rw [h₄, h₂]; exact h.cm5a
    cm5b := by rw [h₅, h₁]; exact h.cm5b }

end ModelCategory

end HomotopicalAlgebra
