import TopCatModelCategory.SSet.AnodyneExtensions
import TopCatModelCategory.SSet.Monoidal

universe u

open CategoryTheory MonoidalCategory HomotopicalAlgebra Limits

namespace SSet

variable {A B X Y : SSet.{u}}

instance (p : X ⟶ Y) [Fibration p] :
    Fibration ((ihom A).map p) := sorry

instance (f : A ⟶ B) [Mono f] [IsFibrant X] :
    Fibration ((MonoidalClosed.pre f).app X) :=
  sorry

instance {A X : SSet.{u}} [IsFibrant X] : IsFibrant (A ⟶[SSet] X) := by
  rw [isFibrant_iff_of_isTerminal ((ihom A).map (terminal.from X))]
  · infer_instance
  · apply isLimitOfHasTerminalOfPreservesLimit

end SSet
