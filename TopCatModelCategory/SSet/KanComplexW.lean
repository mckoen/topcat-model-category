import TopCatModelCategory.SSet.Homotopy

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

namespace KanComplex

def W : MorphismProperty SSet.{u} := fun X Y f ↦
  ∃ (_ : IsFibrant X) (_ : IsFibrant Y),
    (mapFundamentalGroupoid f).IsEquivalence ∧
      ∀ (n : ℕ) (x : X _[0]) (y : Y _[0]) (h : f.app _ x = y),
        Function.Bijective (mapπ f n x y h)

variable {X Y : SSet.{u}} (f : X ⟶ Y)

lemma W.mk [IsFibrant X] [IsFibrant Y] (h₀₁ : (mapFundamentalGroupoid f).IsEquivalence)
    (h : ∀ (n : ℕ) (x : X _[0]) (y : Y _[0]) (h : f.app _ x = y),
      Function.Bijective (mapπ f n x y h)) : W f :=
  ⟨inferInstance, inferInstance, h₀₁, h⟩

variable {f}

lemma W.isFibrant_src (hf : W f) : IsFibrant X := hf.choose

lemma W.isFibrant_tgt (hf : W f) : IsFibrant Y := hf.choose_spec.choose

lemma W.isEquivalence [IsFibrant X] [IsFibrant Y] (hf : W f) :
    (mapFundamentalGroupoid f).IsEquivalence :=
  hf.choose_spec.choose_spec.1

lemma W.bijective (hf : W f) (n : ℕ) (x : X _[0]) (y : Y _[0]) (h : f.app _ x = y) :
    Function.Bijective (mapπ f n x y h) :=
  hf.choose_spec.choose_spec.2 n x y h

variable (f) in
lemma W.of_iso [IsIso f] [IsFibrant X] [IsFibrant Y] : W f := by
  apply W.mk
  · infer_instance
  · intro n x y h
    exact (mapπEquivOfIso (asIso f) n x y h).bijective

variable (X) in
lemma W.id [IsFibrant X] : W (𝟙 X) := W.of_iso _

variable {Z : SSet.{u}} {g : Y ⟶ Z}

lemma W.comp (hf : W f) (hg : W g) : W (f ≫ g) := by
  have := hf.isFibrant_src
  have := hf.isFibrant_tgt
  have := hg.isFibrant_tgt
  apply W.mk
  · have := hf.isEquivalence
    have := hg.isEquivalence
    exact Functor.isEquivalence_of_iso
      (compMapFundamentalGroupoidIso f g).symm
  · rintro n x _ rfl
    dsimp
    rw [← mapπ_comp_mapπ f n x _ rfl g _ rfl]
    exact (hg.bijective n _ _ rfl).comp (hf.bijective n x _ rfl)

instance : W.{u}.IsStableUnderComposition where
  comp_mem _ _ hf hg := hf.comp hg

end KanComplex

end SSet
