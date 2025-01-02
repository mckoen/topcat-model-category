import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument

universe w v v' u u'

local instance Cardinal.aleph0_isRegular : Fact Cardinal.aleph0.{w}.IsRegular where
  out := Cardinal.isRegular_aleph0

noncomputable local instance Cardinal.orderbot_aleph0_ord_to_type :
    OrderBot Cardinal.aleph0.ord.toType :=
  Cardinal.IsRegular.orderBotOrdToType Cardinal.isRegular_aleph0

namespace CategoryTheory.MorphismProperty

attribute [local instance] Cardinal.orderbot_aleph0_ord_to_type

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

lemma monotone_coproducts {W₁ W₂ : MorphismProperty C} (h : W₁ ≤ W₂) :
    coproducts.{w} W₁ ≤ coproducts.{w} W₂ := by
  intro A B f hf
  rw [coproducts_iff] at hf ⊢
  obtain ⟨J, hf⟩ := hf
  exact ⟨J, monotone_colimitsOfShape h _ _ hf⟩

lemma transfiniteCompositionsOfShape_aleph0 (W : MorphismProperty C) :
    W.transfiniteCompositionsOfShape Cardinal.aleph0.{w}.ord.toType =
      W.transfiniteCompositionsOfShape ℕ := sorry

@[simp]
lemma min_iff (W₁ W₂ : MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    (W₁ ⊓ W₂) f ↔ W₁ f ∧ W₂ f := Iff.rfl

@[simp]
lemma sInf_iff (S : Set (MorphismProperty C)) {X Y : C} (f : X ⟶ Y) :
    sInf S f ↔ ∀ (W : S), W.1 f := by
  dsimp [sInf, iInf]
  aesop

@[simp]
lemma max_iff (W₁ W₂ : MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    (W₁ ⊔ W₂) f ↔ W₁ f ∨ W₂ f := Iff.rfl

instance isSmall_sup {ι : Type w'} (W : ι → MorphismProperty C) [∀ i, IsSmall.{w} (W i)]
    [Small.{w} ι] :
    IsSmall.{w} (⨆ i, W i) := sorry

section

variable {ι : Sort*} (W : ι → MorphismProperty C)

@[simp]
lemma iInf_iff {X Y : C} (f : X ⟶ Y) :
    iInf W f ↔ ∀ i, W i f := by
  dsimp [sInf, iInf]
  aesop

instance [∀ i, (W i).ContainsIdentities] : (⨅ (i : ι), W i).ContainsIdentities where
  id_mem X := by
    simp only [iInf_iff]
    intro i
    apply id_mem

instance [∀ i, (W i).IsStableUnderComposition] : (⨅ (i : ι), W i).IsStableUnderComposition where
  comp_mem f g hf hg := by
    simp only [iInf_iff] at hf hg ⊢
    intro i
    exact comp_mem _ _ _ (hf i) (hg i)

instance [∀ i, (W i).IsMultiplicative] : (⨅ (i : ι), W i).IsMultiplicative where

instance [∀ i, (W i).IsStableUnderRetracts] : (⨅ (i : ι), W i).IsStableUnderRetracts where
  of_retract hfg hg := by
    simp only [iInf_iff] at hg ⊢
    intro i
    exact of_retract hfg (hg i)

instance [∀ i, (W i).HasTwoOutOfThreeProperty] : (⨅ (i : ι), W i).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := by
    simp only [iInf_iff] at hg hfg ⊢
    intro i
    exact (W i).of_postcomp f g (hg i) (hfg i)
  of_precomp f g hf hfg := by
    simp only [iInf_iff] at hf hfg ⊢
    intro i
    exact (W i).of_precomp f g (hf i) (hfg i)

end

section

variable (W₁ W₂ : MorphismProperty C)

instance [W₁.IsStableUnderRetracts] [W₂.IsStableUnderRetracts] :
    (W₁ ⊓ W₂).IsStableUnderRetracts where
  of_retract hfg hg := ⟨of_retract hfg hg.1, of_retract hfg hg.2⟩

instance [W₁.HasTwoOutOfThreeProperty] [W₂.HasTwoOutOfThreeProperty] :
    (W₁ ⊓ W₂).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := ⟨W₁.of_postcomp f g hg.1 hfg.1, W₂.of_postcomp f g hg.2 hfg.2⟩
  of_precomp f g hf hfg := ⟨W₁.of_precomp f g hf.1 hfg.1, W₂.of_precomp f g hf.2 hfg.2⟩

end

section

variable (W : MorphismProperty D) (F : C ⥤ D)

instance [W.IsStableUnderRetracts] : (W.inverseImage F).IsStableUnderRetracts where
  of_retract r h := W.of_retract (r.map F.mapArrow) h

end

end CategoryTheory.MorphismProperty
