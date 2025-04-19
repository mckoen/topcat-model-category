import TopCatModelCategory.TopCat.Colimits
import TopCatModelCategory.ColimitsType
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

instance : t₁Inclusion.{u}.IsStableUnderCobaseChange where
  of_isPushout {X₁ X₃ X₂ X₄ l t r b} sq hl := by
    exact
      { toIsClosedEmbedding := by
          have H (F) : b ⁻¹' (r '' F) = l '' (t ⁻¹' F) := by
            ext x₃
            simp only [Set.mem_preimage, Set.mem_image]
            constructor
            · rintro ⟨x₂, hx₂, hx₂'⟩
              obtain ⟨x₁, rfl, rfl⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
                (sq.map (forget _)).flip.isColimit hl.injective x₃ x₂).1 hx₂'.symm
              exact ⟨x₁, hx₂, rfl⟩
            · rintro ⟨x₁, hx₁, rfl⟩
              exact ⟨t x₁, hx₁, congr_fun ((forget _).congr_map sq.w) x₁⟩
          have hr : Function.Injective r := by
            simpa only [ConcreteCategory.forget_map_eq_coe,
                MorphismProperty.monomorphisms.iff, mono_iff_injective] using
                MorphismProperty.of_isPushout
                  (P := MorphismProperty.monomorphisms (Type u)) (sq.map (forget _)) (by
                  simpa only [MorphismProperty.monomorphisms.iff,
                    ConcreteCategory.forget_map_eq_coe, mono_iff_injective]
                    using hl.injective)
          have hr' (F : Set X₂) (hF : IsClosed F) : IsClosed (r '' F) := by
            rw [isClosed_iff_of_isPushout sq]
            constructor
            · rwa [hr.preimage_image F]
            · rw [H, ← hl.isClosed_iff_image_isClosed]
              exact IsClosed.preimage (by continuity) hF
          constructor
          · refine ⟨⟨?_⟩, hr⟩
            · rw [TopologicalSpace.ext_iff_isClosed]
              intro F
              rw [isClosed_induced_iff]
              constructor
              · intro hF
                exact ⟨r '' F, hr' _ hF, hr.preimage_image F⟩
              · rintro ⟨G, hG, rfl⟩
                exact IsClosed.preimage (by continuity) hG
          · simpa using hr' ⊤ (by simp)
        isClosed_singleton := by
          intro y hy
          rw [isClosed_iff_of_isPushout sq]
          constructor
          · simpa only [show r ⁻¹' {y} = ∅ by aesop] using isClosed_empty
          · obtain ⟨x₂, rfl⟩ | ⟨x₃, rfl, hx₃⟩ := Types.eq_or_eq_of_isPushout' (sq.map (forget _)) y
            · exact (hy ⟨_, rfl⟩).elim
            · convert hl.isClosed_singleton x₃ hx₃
              ext y₃
              simp only [ConcreteCategory.forget_map_eq_coe, Set.mem_preimage,
                Set.mem_singleton_iff]
              refine ⟨fun h ↦ ?_, by rintro rfl; rfl⟩
              obtain rfl | ⟨x₀, y₀, rfl, rfl, hxy⟩ :=
                (Types.pushoutCocone_inl_eq_inl_iff_of_isColimit
                  (sq.map (forget _)).flip.isColimit hl.injective y₃ x₃).1 h
              · rfl
              · exact (hx₃ ⟨_, rfl⟩).elim }

end t₁Inclusion

end TopCat
