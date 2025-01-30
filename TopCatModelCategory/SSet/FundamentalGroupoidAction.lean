import TopCatModelCategory.SSet.FundamentalGroupoid
import TopCatModelCategory.SSet.HomotopyBasic

universe u

open HomotopicalAlgebra CategoryTheory

namespace SSet

namespace KanComplex

namespace FundamentalGroupoid

@[simps obj]
def action (X : SSet.{u}) [IsFibrant X] (n : ℕ) :
    FundamentalGroupoid X ⥤ Type u where
  obj x := π n X x.pt
  map := sorry
  map_id := sorry
  map_comp := sorry

@[simps]
def actionMap {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) (n : ℕ) :
    action X n ⟶ mapFundamentalGroupoid f ⋙ action Y n where
  app x := mapπ f n x.pt _ rfl
  naturality := sorry

end FundamentalGroupoid

end KanComplex

end SSet
