import TopCatModelCategory.SSet.IsFiniteCoproducts
import Mathlib.CategoryTheory.Presentable.Limits

universe u

open CategoryTheory Limits Simplicial

namespace SSet

variable (X : SSet.{u})

noncomputable abbrev nonDegenerateπSrc : SSet.{u} :=
  ∐ (fun (⟨n, _⟩ : (Σ (_d : ℕ), X.nonDegenerate _d)) ↦ Δ[n])

noncomputable def nonDegenerateπ :
    nonDegenerateπSrc X ⟶ X :=
  Sigma.desc (fun ⟨_, x⟩ ↦ yonedaEquiv.symm x.1)

example [X.IsFinite] : (nonDegenerateπSrc X).IsFinite := inferInstance

end SSet
