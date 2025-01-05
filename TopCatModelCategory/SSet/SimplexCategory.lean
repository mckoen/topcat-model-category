import Mathlib.AlgebraicTopology.SimplexCategory

open CategoryTheory Simplicial

namespace SimplexCategory

lemma surjective_const {n : ℕ} (f : mk 0 ⟶ mk n) :
    ∃ (i : Fin (n + 1)), f = const [0] [n] i :=
  ⟨f.toOrderHom 0, by
    ext j
    fin_cases j
    rfl⟩

end SimplexCategory
