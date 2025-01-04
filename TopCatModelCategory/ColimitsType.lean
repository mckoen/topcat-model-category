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

section

variable {X X' : Type u} (f : X' → X) (A B : Set X) (A' B' : Set X')
  (hA' : A' = f ⁻¹' A ⊓ B') (hB : B = A ⊔ f '' B')

def pushoutCoconeOfPullbackSets :
    PushoutCocone
      (fun ⟨a', ha'⟩ ↦ ⟨f a', by
        rw [hA'] at ha'
        exact ha'.1⟩ : _ ⟶ (A : Type u) )
      (Set.toTypes.map (homOfLE (by rw [hA']; exact inf_le_right)) : (A' : Type u) ⟶ B') :=
  PushoutCocone.mk (W := (B : Type u))
    (Set.toTypes.map (homOfLE (by rw [hB]; exact le_sup_left)) : (A : Type u) ⟶ B)
    (fun ⟨b', hb'⟩ ↦ ⟨f b', by rw [hB]; exact Or.inr (by aesop)⟩) rfl

open Classical in
noncomputable def isColimitPushoutCoconeOfPullbackSets (hf : Function.Injective f) :
    IsColimit (pushoutCoconeOfPullbackSets f A B A' B' hA' hB) := by
  let g₁ : (A' : Type u) ⟶ A := fun ⟨a', ha'⟩ ↦ ⟨f a', by
        rw [hA'] at ha'
        exact ha'.1⟩
  let g₂ : (A' : Type u) ⟶ B' :=
    (Set.toTypes.map (homOfLE (by rw [hA']; exact inf_le_right)) : (A' : Type u) ⟶ B')
  have imp {b : X} (hb : b ∈ B) (hb' : b ∉ A) : b ∈ f '' B' := by
    simp only [hB, Set.sup_eq_union, Set.mem_union] at hb
    tauto
  let desc (s : PushoutCocone g₁ g₂) : (B : Type u) ⟶ s.pt := fun ⟨b, hb⟩ ↦
    if hb' : b ∈ A then
      s.inl ⟨b, hb'⟩
    else
      s.inr ⟨(imp hb hb').choose, (imp hb hb').choose_spec.1⟩
  have inl_desc_apply (s) (a : A) : desc s ⟨a, by
    rw [hB]
    exact Or.inl a.2⟩ = s.inl a := dif_pos a.2
  have inr_desc_apply (s) (b' : B') : desc s ⟨f b', by
      rw [hB]
      exact Or.inr ⟨b'.1, b'.2, rfl⟩⟩ = s.inr b' := by
    obtain ⟨b', hb'⟩ := b'
    dsimp [desc]
    split_ifs with hb''
    · exact congr_fun s.condition ⟨b', by rw [hA']; exact ⟨hb'', hb'⟩⟩
    · apply congr_arg
      ext
      refine hf (imp ?_ hb'').choose_spec.2
      rw [hB]
      exact Or.inr ⟨b', hb', rfl⟩
  refine PushoutCocone.IsColimit.mk _ desc
    (fun s ↦ by ext; apply inl_desc_apply)
    (fun s ↦ by ext; apply inr_desc_apply)
    (fun s m h₁ h₂ ↦ ?_)
  ext ⟨b, hb⟩
  dsimp
  by_cases hb' : b ∈ f '' B'
  · obtain ⟨b', hb', rfl⟩ := hb'
    exact (congr_fun h₂ ⟨b', hb'⟩).trans (inr_desc_apply s ⟨b', hb'⟩ ).symm
  · have hb : b ∈ A := by
      simp only [hB, Set.sup_eq_union, Set.mem_union] at hb
      tauto
    exact (congr_fun h₁ ⟨b, hb⟩).trans (inl_desc_apply s ⟨b, hb⟩).symm

end

section

variable {X : Type u} {A₁ A₂ A₃ A₄ : Set X} (sq : Lattice.BicartSq A₁ A₂ A₃ A₄)

def pushoutCoconeOfBicartSqOfSets :
    PushoutCocone (Set.toTypes.map (homOfLE sq.le₁₂))
      (Set.toTypes.map (homOfLE sq.le₁₃)) :=
  PushoutCocone.mk _ _ (sq.commSq.map Set.toTypes).w

noncomputable def isColimitPushoutCoconeOfBicartSqOfSets :
    IsColimit (pushoutCoconeOfBicartSqOfSets sq) :=
  isColimitPushoutCoconeOfPullbackSets id A₂ A₄ A₁ A₃
    sq.min_eq.symm (by simpa using sq.max_eq.symm) (fun _ _ h ↦ h)

end

end Pushouts

end CategoryTheory.Limits.Types
