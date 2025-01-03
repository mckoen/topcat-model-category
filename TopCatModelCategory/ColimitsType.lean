import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.Data.Set.Lattice

universe u

open CategoryTheory

namespace Lattice

variable {T : Type u} (x₁ x₂ x₃ x₄ : T) [Lattice T]

structure BicartSq where
  max_eq : x₂ ⊔ x₃ = x₄
  min_eq : x₂ ⊓ x₃ = x₁

namespace BicartSq

variable {x₁ x₂ x₃ x₄ : T} (sq : BicartSq x₁ x₂ x₃ x₄)

include sq
lemma le₁₂ : x₁ ≤ x₂ := by rw [← sq.min_eq]; exact inf_le_left
lemma le₁₃ : x₁ ≤ x₃ := by rw [← sq.min_eq]; exact inf_le_right
lemma le₂₄ : x₂ ≤ x₄ := by rw [← sq.max_eq]; exact le_sup_left
lemma le₃₄ : x₃ ≤ x₄ := by rw [← sq.max_eq]; exact le_sup_right

-- the associated commutative square in `T`
lemma commSq : CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) := ⟨rfl⟩

end BicartSq

end Lattice

@[simps obj map]
def Set.toTypes {X : Type u} : Set X ⥤ Type u where
  obj S := S
  map {S T} f := fun ⟨x, hx⟩ ↦ ⟨x, leOfHom f hx⟩

namespace CategoryTheory.Limits.Types

section Pushouts

variable {X : Type u} {A₁ A₂ A₃ A₄ : Set X} (sq : Lattice.BicartSq A₁ A₂ A₃ A₄)

#check sq.commSq.map Set.toTypes
def pushoutCoconeOfBicartSqOfSets :
    PushoutCocone (Set.toTypes.map (homOfLE sq.le₁₂))
      (Set.toTypes.map (homOfLE sq.le₁₃)) :=
  PushoutCocone.mk _ _ (sq.commSq.map Set.toTypes).w

namespace isColimitPushoutCoconeOfBicartSqOfSets

variable (s : PushoutCocone (Set.toTypes.map (homOfLE sq.le₁₂))
    (Set.toTypes.map (homOfLE sq.le₁₃)))

open Classical in
noncomputable def desc :
    (A₄ : Type u) ⟶ s.pt := fun ⟨x, hx⟩ ↦
  if h : x ∈ A₂ then s.inl ⟨x, h⟩ else s.inr ⟨x, by
    simp [← sq.max_eq] at hx
    tauto⟩

@[simp]
lemma inl_desc_apply (x : A₂) : desc sq s ⟨x, by simp [← sq.max_eq]⟩ = s.inl x := by
  dsimp only [desc]
  rw [dif_pos]

@[simp]
lemma inr_desc_apply (x : A₃) : desc sq s ⟨x, by simp [← sq.max_eq]⟩ = s.inr x := by
  dsimp only [desc]
  by_cases h : x.1 ∈ A₂
  · rw [dif_pos h]
    exact congr_fun s.condition ⟨x, by simp [← sq.min_eq]; tauto⟩
  · rw [dif_neg h]

end isColimitPushoutCoconeOfBicartSqOfSets

open isColimitPushoutCoconeOfBicartSqOfSets in
noncomputable def isColimitPushoutCoconeOfBicartSqOfSets :
    IsColimit (pushoutCoconeOfBicartSqOfSets sq) := by
  refine PushoutCocone.IsColimit.mk _
    (fun s ↦ desc sq s) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)
  · ext (x : A₂)
    simp
  · ext (x : A₃)
    simp
  · ext ⟨x, hx⟩
    rw [← sq.max_eq] at hx
    obtain h₃ | h₄ := hx
    · dsimp
      rw [inl_desc_apply sq s ⟨x, h₃⟩]
      exact congr_fun h₁ ⟨x, h₃⟩
    · dsimp
      rw [inr_desc_apply sq s ⟨x, h₄⟩]
      exact congr_fun h₂ ⟨x, h₄⟩

end Pushouts

end CategoryTheory.Limits.Types
