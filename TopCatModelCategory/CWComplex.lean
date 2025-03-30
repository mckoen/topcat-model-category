import TopCatModelCategory.CellComplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Category.TopCat.Limits.Basic

universe u

/-open CategoryTheory Limits HomotopicalAlgebra

namespace TopCat

namespace RelativeCWComplex

noncomputable def disk (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : EuclideanSpace ℝ <| Fin <| n) 1

-- for `n > 0`, this is a sphere
noncomputable def diskBoundary (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| n) 1

scoped prefix:arg "𝔻 " => disk
scoped prefix:arg "∂𝔻 " => diskBoundary

def diskBoundaryInclusion (n : ℕ) : ∂𝔻 n ⟶ 𝔻 n where
  toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
  continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
    rw [isOpen_induced_iff, ← hst, ← hrs]
    tauto⟩

@[simp]
def basicCell (n : ℕ) (_ : Unit) : ∂𝔻 n ⟶ 𝔻 n := diskBoundaryInclusion n

end RelativeCWComplex

open RelativeCWComplex in
abbrev RelativeCWComplex {X Y : TopCat.{u}} (f : X ⟶ Y) := RelativeCellComplex basicCell f
abbrev CWComplex (X : TopCat.{u}) := RelativeCWComplex (initial.to X)

end TopCat-/
