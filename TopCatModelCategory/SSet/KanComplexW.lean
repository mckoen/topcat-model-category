import TopCatModelCategory.SSet.Homotopy

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

namespace KanComplex

def mapFundamentalGroupoid {X Y : SSet.{u}}
    (f : X ⟶ Y) [IsFibrant X] [IsFibrant Y] :
    FundamentalGroupoid X ⥤ FundamentalGroupoid Y := sorry

def W : MorphismProperty SSet.{u} := fun X Y f ↦
  ∃ (_ : IsFibrant X) (_ : IsFibrant Y),
    (mapFundamentalGroupoid f).IsEquivalence ∧
      ∀ (n : ℕ) (x : X _[0]) (y : Y _[0]) (h : f.app _ x = y),
        Function.Bijective (mapπ f n x y h)

variable {X Y : SSet.{u}} {f : X ⟶ Y}

lemma W.isEquivalence [IsFibrant X] [IsFibrant Y] (hf : W f) :
    (mapFundamentalGroupoid f).IsEquivalence :=
  hf.choose_spec.choose_spec.1

lemma W.bijective (hf : W f) (n : ℕ) (x : X _[0]) (y : Y _[0]) (h : f.app _ x = y) :
    Function.Bijective (mapπ f n x y h) :=
  hf.choose_spec.choose_spec.2 n x y h

end KanComplex

end SSet
