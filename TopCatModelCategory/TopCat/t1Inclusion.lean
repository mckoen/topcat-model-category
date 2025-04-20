import TopCatModelCategory.TopCat.ClosedEmbeddings
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.Topology.Category.TopCat.Limits.Basic

universe u

open CategoryTheory Topology Limits MorphismProperty

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

section

variable {J : Type u'} {X₁ : J → TopCat.{u}} {X₂ : J → TopCat.{u}}
  (f : ∀ j, X₁ j ⟶ X₂ j) {c₁ : Cofan X₁} (h₁ : IsColimit c₁) {c₂ : Cofan X₂}
  (h₂ : IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, c₁.inj j ≫ φ = f j ≫ c₂.inj j)

include h₁ h₂ hφ in
lemma isT₁Inclusion_of_isColimit (hf : ∀ j, IsT₁Inclusion (f j)) :
    IsT₁Inclusion φ where
  toIsClosedEmbedding := isClosedEmbedding_of_isColimit f h₁ h₂ φ hφ
    (fun j ↦ (hf j).toIsClosedEmbedding)
  isClosed_singleton y hy := by
    obtain ⟨⟨i⟩, (y : X₂ i), rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget _) h₂) y
    rw [isClosed_iff_of_isColimit _ h₂]
    rintro ⟨j⟩
    by_cases hj : i = j
    · subst hj
      convert (hf i).isClosed_singleton y (by
        rintro ⟨x, rfl⟩
        exact hy ⟨c₁.inj i x, congr_fun ((forget _).congr_map (hφ i)) x⟩)
      convert (cofanInj_injective_of_isColimit h₂ i).preimage_image {y}
      dsimp
      simp only [Set.image_singleton, Set.singleton_eq_singleton_iff]
      rfl
    · convert isClosed_empty
      ext (x : X₂ j)
      dsimp
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hj (eq_cofanInj_apply_eq_of_isColimit h₂ _ _ h.symm)

end

instance : t₁Inclusions.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hl := isT₁Inclusion_of_isPushout sq.flip hl

instance : IsStableUnderCoproducts.{u'} t₁Inclusions.{u} where
  isStableUnderCoproductsOfShape J := by
    apply IsStableUnderCoproductsOfShape.mk
    intro X₁ X₂ _ _ f hf
    exact isT₁Inclusion_of_isColimit f (colimit.isColimit _)
      (colimit.isColimit _) _ (fun j ↦ colimit.ι_desc _ _) hf

end t₁Inclusions

end TopCat
