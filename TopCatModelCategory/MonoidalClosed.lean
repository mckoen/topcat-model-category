import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C]

namespace MonoidalCategory

variable [BraidedCategory C]

@[simps!]
def tensorLeftIsoTensorRight (X : C) :
    tensorLeft X ≅ tensorRight X :=
  NatIso.ofComponents (fun _ ↦ β_ _ _)

end MonoidalCategory

open MonoidalCategory

namespace MonoidalClosed

instance (X : C) [Closed X] : (tensorLeft X).IsLeftAdjoint :=
  (ihom.adjunction X).isLeftAdjoint

instance (X : C) [Closed X] : (ihom X).IsRightAdjoint :=
  (ihom.adjunction X).isRightAdjoint

instance (X : C) [Closed X] [BraidedCategory C]: (tensorRight X).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (tensorLeftIsoTensorRight X)

instance (X : C) [MonoidalClosed C] : (tensorLeft X).IsLeftAdjoint :=
  inferInstance

end MonoidalClosed

end CategoryTheory
