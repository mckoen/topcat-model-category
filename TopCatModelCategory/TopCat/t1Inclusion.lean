import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.Topology.Category.TopCat.Basic

universe u

open CategoryTheory Topology

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

def t₁Inclusion : MorphismProperty TopCat.{u} :=
  fun _ _ f ↦ IsT₁Inclusion f

namespace t₁Inclusion

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : t₁Inclusion f)

instance : t₁Inclusion.{u}.IsMultiplicative where
  id_mem _ := IsT₁Inclusion.id _
  comp_mem _ _ hf hg := hg.comp hf

instance : t₁Inclusion.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ f (_ : IsIso f) ↦
    IsT₁Inclusion.of_homeo (TopCat.homeoOfIso (asIso f)))

end t₁Inclusion

end TopCat
