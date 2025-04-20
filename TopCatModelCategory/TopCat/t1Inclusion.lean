import TopCatModelCategory.TopCat.ClosedEmbeddings
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.Topology.Category.TopCat.Limits.Basic

universe u

open CategoryTheory Topology Limits

namespace Topology

-- This was also formalized by Reid Barton
-- Reference is [Hovey, *Model categories*, 2.4]

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[mk_iff]
structure IsT₁Inclusion (f : X → Y) : Prop extends IsClosedEmbedding f where
  isClosed_singleton  (y : Y) (_ : y ∉ Set.range f) : IsClosed {y}

lemma IsT₁Inclusion.of_homeo (e : Homeomorph X Y) :
    IsT₁Inclusion e where
  toIsClosedEmbedding := Homeomorph.isClosedEmbedding e
  isClosed_singleton _ hy := by simp at hy

variable (X) in
lemma IsT₁Inclusion.id : IsT₁Inclusion (id : X → X) :=
  IsT₁Inclusion.of_homeo (Homeomorph.refl X)

lemma IsT₁Inclusion.comp {g : Y → Z} {f : X → Y}
    (hg : IsT₁Inclusion g) (hf : IsT₁Inclusion f) :
    IsT₁Inclusion (g.comp f) where
  toIsClosedEmbedding := hg.toIsClosedEmbedding.comp hf.toIsClosedEmbedding
  isClosed_singleton z hz := by
    by_cases hz' : z ∈ Set.range g
    · obtain ⟨y, rfl⟩ := hz'
      convert
        (IsClosedEmbedding.isClosed_iff_image_isClosed hg.toIsClosedEmbedding).1
          (hf.isClosed_singleton y (by rintro ⟨x, rfl⟩; exact hz ⟨x, rfl⟩))
      aesop
    · exact hg.isClosed_singleton _ hz'

end Topology

namespace TopCat

def t₁Inclusions : MorphismProperty TopCat.{u} :=
  fun _ _ f ↦ IsT₁Inclusion f

namespace t₁Inclusions

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : t₁Inclusions f)

instance : t₁Inclusions.{u}.IsMultiplicative where
  id_mem _ := IsT₁Inclusion.id _
  comp_mem _ _ hf hg := hg.comp hf

instance : t₁Inclusions.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ f (_ : IsIso f) ↦
    IsT₁Inclusion.of_homeo (TopCat.homeoOfIso (asIso f)))

section

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

lemma isT₁Inclusion_of_isPushout (sq : IsPushout t l r b)
    (ht : IsT₁Inclusion t) :
    IsT₁Inclusion b where
  toIsClosedEmbedding := isClosedEmbedding_of_isPushout sq ht.toIsClosedEmbedding
  isClosed_singleton y hy := by
    rw [isClosed_iff_of_isPushout sq]
    constructor
    · obtain ⟨x₃, rfl⟩ | ⟨x₂, rfl, hx₂⟩ := Types.eq_or_eq_of_isPushout' (sq.flip.map (forget _)) y
      · exact (hy ⟨_, rfl⟩).elim
      · convert ht.isClosed_singleton x₂ hx₂
        ext y₂
        simp only [ConcreteCategory.forget_map_eq_coe, Set.mem_preimage, Set.mem_singleton_iff]
        refine ⟨fun h ↦ ?_, by rintro rfl; rfl⟩
        obtain rfl | ⟨x₀, y₀, rfl, rfl, hxy⟩ := (Types.pushoutCocone_inl_eq_inl_iff_of_isColimit
          (sq.map (forget _)).isColimit ht.injective y₂ x₂).1 h
        · rfl
        · exact (hx₂ ⟨_, rfl⟩).elim
    · simpa only [show b ⁻¹' {y} = ∅ by aesop] using isClosed_empty

end

instance : t₁Inclusions.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hl := isT₁Inclusion_of_isPushout sq.flip hl

end t₁Inclusions

end TopCat
