import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Limits.TypesFiltered
import Mathlib.CategoryTheory.MorphismProperty.Composition
import TopCatModelCategory.SSet.Monomorphisms
import TopCatModelCategory.ColimitsType
import TopCatModelCategory.TopCat.Colimits

universe u

open CategoryTheory Topology Limits MorphismProperty

namespace TopCat

def closedEmbeddings : MorphismProperty TopCat.{u} :=
  fun _ _ f ↦ IsClosedEmbedding f

lemma closedEmbeddings_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    closedEmbeddings f ↔ IsClosedEmbedding f := Iff.rfl

lemma closedEmbedding_le_inverseImage_monomorphisms :
    closedEmbeddings.{u} ≤ (monomorphisms (Type u)).inverseImage (forget _) :=
  fun _ _ _ hf ↦ by simpa [CategoryTheory.mono_iff_injective] using hf.injective

instance : closedEmbeddings.{u}.IsMultiplicative where
  id_mem _ := IsClosedEmbedding.id
  comp_mem _ _ hf hg := hg.comp hf

lemma isClosedEmbedding_of_isIso {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso f] :
    IsClosedEmbedding f := (homeoOfIso (asIso f)).isClosedEmbedding

instance : closedEmbeddings.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (by
    intro X Y f hf
    have : IsIso f := by assumption
    apply isClosedEmbedding_of_isIso)

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

section

variable {J : Type u'} {X₁ : J → TopCat.{u}} {X₂ : J → TopCat.{u}}
  (f : ∀ j, X₁ j ⟶ X₂ j) {c₁ : Cofan X₁} (h₁ : IsColimit c₁) {c₂ : Cofan X₂}
  (h₂ : IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, c₁.inj j ≫ φ = f j ≫ c₂.inj j)

include h₁ in
lemma cofanInj_injective_of_isColimit (j : J) : Function.Injective (c₁.inj j) :=
  Types.cofanInj_injective_of_isColimit
    (isColimitCofanMkObjOfIsColimit (forget _) _ (fun j ↦ c₁.inj j) h₁) j

include h₁ in
lemma eq_cofanInj_apply_eq_of_isColimit {i j : J} (x : X₁ i) (y : X₁ j)
    (h : c₁.inj i x = c₁.inj j y) : i = j :=
  Types.eq_cofanInj_apply_eq_of_isColimit
    (isColimitCofanMkObjOfIsColimit (forget _) _ (fun j ↦ c₁.inj j) h₁) _ _ h

include h₁ h₂ hφ

lemma injective_of_coproducts (hf : ∀ j, Function.Injective (f j)) :
    Function.Injective φ := by
  have := ((monomorphisms (Type u)).isStableUnderCoproductsOfShape_of_isStableUnderCoproducts J)
    (Discrete.functor X₁ ⋙ forget _) (Discrete.functor X₂ ⋙ forget _) _ _
    (isColimitOfPreserves (forget _) h₁) (isColimitOfPreserves (forget _) h₂)
    (whiskerRight (Discrete.natTrans (fun ⟨j⟩ ↦ f j)) _) (fun ⟨j⟩ ↦ by
      simpa only [monomorphisms.iff, CategoryTheory.mono_iff_injective] using hf j)
  rw [← CategoryTheory.mono_iff_injective]
  convert this
  apply (isColimitOfPreserves (forget _) h₁).hom_ext
  rintro ⟨j⟩
  rw [IsColimit.fac]
  ext x
  exact congr_fun ((forget _).congr_map (hφ j)) x

lemma preimage_image_eq_of_coproducts
    (j : J) (F : Set (X₂ j)) :
    φ ⁻¹' (c₂.inj j '' F) = c₁.inj j '' ((f j) ⁻¹' F) :=
  Types.preimage_image_eq_of_coproducts
    (isColimitCofanMkObjOfIsColimit (forget _) _ (fun j ↦ c₁.inj j) h₁)
    (isColimitCofanMkObjOfIsColimit (forget _) _ (fun j ↦ c₂.inj j) h₂) (fun j ↦ f j)
    ((forget _).map φ) (fun j ↦ by
      ext x
      exact congr_fun ((forget _).congr_map (hφ j)) x) j F

lemma isInducing_of_coproducts (hf : ∀ j, IsInducing (f j)) :
    IsInducing φ := by
  have := h₁
  have := h₂
  have := hφ
  constructor
  rw [TopologicalSpace.ext_iff_isClosed]
  intro F
  rw [isClosed_induced_iff]
  constructor
  · intro hF
    let G (j : J) := (c₁.inj j) ⁻¹' F
    have hG (j : J) : IsClosed (G j) := (isClosed_iff_of_isColimit _ h₁ F).1 hF ⟨j⟩
    simp only [fun j ↦ (hf j).eq_induced, isClosed_induced_iff] at hG
    let W (j : J) := (hG j).choose
    have hW (j : J) : IsClosed (W j) := (hG j).choose_spec.1
    have hW' (j : J) : (f j) ⁻¹' (W j) = G j := (hG j).choose_spec.2
    refine ⟨⨆ (j : J), c₂.inj j '' (W j), ?_, ?_⟩
    · rw [isClosed_iff_of_isColimit _ h₂]
      rintro ⟨j⟩
      simp only [Discrete.functor_obj_eq_as, Functor.const_obj_obj, Set.iSup_eq_iUnion,
        Set.preimage_iUnion]
      convert hW j
      ext x₂
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨i, y₂, hy₂, h⟩
        obtain rfl := eq_cofanInj_apply_eq_of_isColimit h₂ _ _ h
        obtain rfl := cofanInj_injective_of_isColimit h₂ i h
        exact hy₂
      · rintro hx₂
        exact ⟨j, x₂, hx₂, rfl⟩
    · simp only [Set.iSup_eq_iUnion, Set.preimage_iUnion,
        preimage_image_eq_of_coproducts f h₁ h₂ φ hφ, hW']
      ext x₁
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage, G]
      constructor
      · rintro ⟨j, y, hy, rfl⟩
        exact hy
      · intro hx₁
        obtain ⟨⟨j⟩, (x : X₁ j), rfl⟩ := Types.jointly_surjective_of_isColimit
          (isColimitCofanMkObjOfIsColimit (forget _) _ (fun j ↦ c₁.inj j) h₁) x₁
        dsimp
        exact ⟨j, x, hx₁, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    exact IsClosed.preimage (by continuity) hG

lemma isClosedEmbedding_of_isColimit (hf : ∀ j, IsClosedEmbedding (f j)) :
    IsClosedEmbedding φ where
  toIsInducing := isInducing_of_coproducts f h₁ h₂ φ hφ (fun j ↦ (hf j).toIsInducing)
  injective := injective_of_coproducts f h₁ h₂ φ hφ (fun j ↦ (hf j).injective)
  isClosed_range := by
    rw [isClosed_iff_of_isColimit _ h₂]
    rintro ⟨j⟩
    convert (hf j).isClosed_range
    ext (x₂ : X₂ j)
    dsimp
    simp only [Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨x₁, hx⟩
      obtain ⟨⟨j'⟩, (x₁ : X₁ j'), rfl⟩ := Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget _) h₁) x₁
      replace hx : φ (c₁.inj j' x₁) = c₂.inj j x₂ := hx
      have : c₂.inj j' (f j' x₁) = c₂.inj j x₂ := by
        rw [← hx]
        exact congr_fun ((forget _).congr_map (hφ j').symm) x₁
      obtain rfl : j = j' := eq_cofanInj_apply_eq_of_isColimit h₂ _ _ this.symm
      exact ⟨x₁, cofanInj_injective_of_isColimit h₂ j this⟩
    · rintro ⟨x₁, rfl⟩
      exact ⟨c₁.inj j x₁, congr_fun ((forget _).congr_map (hφ j)) x₁⟩

end

section

variable {J : Type u'} [LinearOrder J] [OrderBot J]

lemma isClosedEmbedding_of_transfiniteCompositionOfShape_aux
    {X : J ⥤ TopCat.{u}} {c : Cocone X} (hc : IsColimit c)
    (hX : ∀ (j : J), IsClosedEmbedding (X.map (homOfLE bot_le : ⊥ ⟶ j)))
    (h' : ∀ ⦃j j' : J⦄ (f : j ⟶ j'), Function.Injective (X.map f)) :
    IsClosedEmbedding (c.ι.app ⊥) := by
  have inj (j : J) : Function.Injective (c.ι.app j) := fun x₁ x₂ h ↦ by
    obtain ⟨k, g, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget _) hc) _ _).1 h
    exact h' _ hk
  have closed {F : Set (X.obj ⊥)} (hF : IsClosed F) :
      IsClosed (c.ι.app ⊥ '' F) := by
    rw [isClosed_iff_of_isColimit c hc]
    intro j
    convert (hX j).isClosedMap _ hF
    ext x
    simp only [Set.mem_preimage, Set.mem_image, homOfLE_leOfHom]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨y, hy, inj _ ?_⟩
      rw [← h]
      exact congr_fun ((forget _).congr_map (c.w (homOfLE bot_le : ⊥ ⟶ j))) y
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, congr_fun ((forget _).congr_map (c.w (homOfLE bot_le : ⊥ ⟶ j)).symm) y⟩
  exact {
    eq_induced := by
      rw [TopologicalSpace.ext_iff_isClosed]
      intro F
      simp only [isClosed_induced_iff]
      constructor
      · intro hF
        exact ⟨c.ι.app ⊥ '' F, closed hF, (inj ⊥).preimage_image F⟩
      · rintro ⟨V, hV, rfl⟩
        exact IsClosed.preimage (by continuity) hV
    injective := inj ⊥
    isClosed_range := by simpa using closed isClosed_univ }

instance (J : Type*) [LinearOrder J] :
  PreservesWellOrderContinuousOfShape J (forget TopCat.{u}) where

lemma isClosedEmbedding_of_transfiniteCompositionOfShape
    [WellFoundedLT J] [SuccOrder J] {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : closedEmbeddings.{u}.TransfiniteCompositionOfShape J f) :
    IsClosedEmbedding f := by
  have inj ⦃j j' : J⦄ (g : j ⟶ j') : Function.Injective (hf.F.map g) := by
    rw [← CategoryTheory.mono_iff_injective]
    exact MorphismProperty.transfiniteCompositionsOfShape_le _ _ _
      ((((hf.ici j).iic ⟨j', leOfHom g⟩).ofLE
        closedEmbedding_le_inverseImage_monomorphisms)).map.mem
  simp only [← hf.fac, Functor.const_obj_obj, hom_comp, ContinuousMap.coe_comp]
  refine IsClosedEmbedding.comp
    (isClosedEmbedding_of_transfiniteCompositionOfShape_aux hf.isColimit (fun j ↦ ?_) inj)
    (isClosedEmbedding_of_isIso _)
  induction j using SuccOrder.limitRecOn with
  | hm j hj =>
    obtain rfl := hj.eq_bot
    simpa using IsClosedEmbedding.id
  | hs j hj hj' =>
    rw [← homOfLE_comp bot_le (Order.le_succ j), Functor.map_comp]
    exact (hf.map_mem j hj).comp hj'
  | hl j hj hj' =>
    letI : OrderBot (Set.Iio j) :=
      { bot := ⟨⊥, hj.bot_lt⟩
        bot_le j := bot_le }
    exact isClosedEmbedding_of_transfiniteCompositionOfShape_aux
      (hf.F.isColimitOfIsWellOrderContinuous j hj) (fun ⟨i, hi⟩ ↦ hj' i hi) (fun _ _ _ ↦ inj _)

end

instance : closedEmbeddings.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hl := isClosedEmbedding_of_isPushout sq.flip hl

instance : IsStableUnderCoproducts.{u'} closedEmbeddings.{u} where
  isStableUnderCoproductsOfShape J := by
    apply IsStableUnderCoproductsOfShape.mk
    intro X₁ X₂ _ _ f hf
    exact isClosedEmbedding_of_isColimit f (colimit.isColimit _)
      (colimit.isColimit _) _ (fun j ↦ colimit.ι_desc _ _) hf

instance : IsStableUnderTransfiniteComposition.{u'} closedEmbeddings.{u} where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ :=
    ⟨fun _ _ _ ⟨hf⟩ ↦ isClosedEmbedding_of_transfiniteCompositionOfShape hf⟩

end TopCat
