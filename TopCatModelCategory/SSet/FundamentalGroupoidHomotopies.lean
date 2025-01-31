import TopCatModelCategory.SSet.FundamentalGroupoid

universe u

open HomotopicalAlgebra

namespace SSet

variable {X : SSet.{u}} [IsFibrant X]

namespace KanComplex

namespace FundamentalGroupoid

variable {x₀ x₁ x₂ x₃ : FundamentalGroupoid X}

namespace Path

def HomotopyL (p q : Path x₀ x₁) := CompStruct p (Path.id x₁) q
def HomotopyR (p q : Path x₀ x₁) := CompStruct (Path.id x₀) p q

section

variable (p q r : Path x₀ x₁)

def HomotopyL.refl : HomotopyL p p := CompStruct.compId p
def HomotopyR.refl : HomotopyR p p := CompStruct.idComp p

variable {p q r}

noncomputable def HomotopyL.symm (h : HomotopyL p q) : HomotopyL q p :=
  CompStruct.assoc h (CompStruct.compId _) (CompStruct.compId p)

noncomputable def HomotopyR.symm (h : HomotopyR p q) : HomotopyR q p :=
  CompStruct.assoc' (CompStruct.idComp _) h (CompStruct.idComp p)

noncomputable def HomotopyL.homotopyR (h : HomotopyL p q) : HomotopyR p q :=
  HomotopyR.symm (CompStruct.assoc' (CompStruct.idComp p) h (CompStruct.compId p))

noncomputable def HomotopyR.homotopyL (h : HomotopyR p q) : HomotopyL p q :=
  HomotopyL.symm (CompStruct.assoc h (CompStruct.compId p) (CompStruct.idComp p))

noncomputable def HomotopyL.trans (h : HomotopyL p q) (h' : HomotopyL q r) :
    HomotopyL p r :=
  CompStruct.assoc (CompStruct.idComp p) h h'.homotopyR

noncomputable def HomotopyR.trans (h : HomotopyR p q) (h' : HomotopyR q r) :
    HomotopyR p r :=
  CompStruct.assoc' h (CompStruct.compId p) h'.homotopyL

end

namespace CompStruct

noncomputable def unique {p₀₁ : Path x₀ x₁} {p₁₂ : Path x₁ x₂} {p₀₂ : Path x₀ x₂}
    (h : CompStruct p₀₁ p₁₂ p₀₂)
    {p₀₁' : Path x₀ x₁} {p₁₂' : Path x₁ x₂} {p₀₂' : Path x₀ x₂}
    (h' : CompStruct p₀₁' p₁₂' p₀₂')
    (h₀₁ : HomotopyL p₀₁ p₀₁') (h₁₂ : HomotopyL p₁₂ p₁₂') :
    HomotopyL p₀₂ p₀₂' :=
  assoc h (compId p₁₂) (assoc (compId p₀₁) h₁₂.homotopyR (assoc' h₀₁ (idComp p₁₂') h'))

end CompStruct

end Path

end FundamentalGroupoid

end KanComplex

end SSet
