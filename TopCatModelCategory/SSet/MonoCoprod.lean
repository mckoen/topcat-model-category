import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import TopCatModelCategory.MonoCoprod

universe u

open CategoryTheory Limits

namespace SSet

instance : MonoCoprod SSet.{u} :=
  inferInstanceAs (MonoCoprod (SimplexCategoryᵒᵖ ⥤ Type u))

end SSet
