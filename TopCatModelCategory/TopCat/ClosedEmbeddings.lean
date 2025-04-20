import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition
import TopCatModelCategory.ColimitsType
import TopCatModelCategory.TopCat.Colimits

universe u

open CategoryTheory Topology Limits

namespace TopCat

def closedEmbeddings : MorphismProperty TopCat.{u} :=
  fun _ _ f ↦ IsClosedEmbedding f

lemma closedEmbeddings_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    closedEmbeddings f ↔ IsClosedEmbedding f := Iff.rfl

instance : closedEmbeddings.{u}.IsMultiplicative where
  id_mem _ := IsClosedEmbedding.id
  comp_mem _ _ hf hg := hg.comp hf

instance : closedEmbeddings.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (by
    intro X Y f hf
    have : IsIso f := by assumption
    exact (homeoOfIso (asIso f)).isClosedEmbedding)

section

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

lemma injective_of_isPushout (sq : IsPushout t l r b) (ht : Function.Injective t) :
    Function.Injective b :=
  Types.injective_of_isPushout (sq.map (forget _)) ht

lemma isClosed_image_iff_of_isPushout (sq : IsPushout t l r b) (ht : IsClosedEmbedding t)
    (F : Set X₃) :
    IsClosed (b '' F) ↔ IsClosed F := by
  have hb := injective_of_isPushout sq ht.injective
  constructor
  · intro hF
    rw [← Function.Injective.preimage_image hb F]
    exact IsClosed.preimage (by continuity) hF
  · intro hF
    rw [isClosed_iff_of_isPushout sq]
    constructor
    · have := Types.preimage_image_eq_of_isPushout (sq.map (forget _)) ht.injective
      dsimp at this
      rw [this, ← ht.isClosed_iff_image_isClosed]
      exact IsClosed.preimage (f := l) (by continuity) hF
    · rwa [Function.Injective.preimage_image hb]

lemma isClosedEmbedding_of_isPushout (sq : IsPushout t l r b)
    (ht : IsClosedEmbedding t) :
    IsClosedEmbedding b where
  injective := injective_of_isPushout sq ht.injective
  eq_induced := by
    rw [TopologicalSpace.ext_iff_isClosed]
    intro F
    rw [isClosed_induced_iff]
    constructor
    · intro hF
      exact ⟨b '' F, by rwa [isClosed_image_iff_of_isPushout sq ht],
        by rw [(injective_of_isPushout sq ht.injective).preimage_image]⟩
    · rintro ⟨G, hG, rfl⟩
      exact IsClosed.preimage (by continuity) hG
  isClosed_range := by simpa using isClosed_image_iff_of_isPushout sq ht (b ⁻¹' ⊤)

end

instance : closedEmbeddings.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hl := isClosedEmbedding_of_isPushout sq.flip hl

end TopCat
