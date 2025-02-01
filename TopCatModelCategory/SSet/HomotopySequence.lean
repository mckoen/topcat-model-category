import TopCatModelCategory.SSet.Homotopy
import TopCatModelCategory.SSet.Fiber

universe u

open HomotopicalAlgebra CategoryTheory Simplicial

namespace SSet

namespace KanComplex

namespace HomotopySequence

variable {E B : SSet.{u}} (p : E ⟶ B) {b : B _[0]}
  {e : E _[0]} (he : p.app _ e = b)

@[simps]
def basePoint : (Subcomplex.fiber p b : SSet) _[0] :=
  ⟨e, by simpa [Subcomplex.fiber]⟩

def map₁ (n : ℕ) : π n (Subcomplex.fiber p b) (basePoint p he) → π n E e := sorry

def map₂ (n : ℕ) : π n E e → π n B b := mapπ p n e b he

variable {p he}

structure DeltaStruct {n : ℕ}
    (s : Subcomplex.RelativeMorphism
      (subcomplexBoundary (n + 1)) _
        (const ⟨b, Subcomplex.mem_ofSimplex_obj b⟩))
    (t : Subcomplex.RelativeMorphism
      (subcomplexBoundary n) _
        (const ⟨_, Subcomplex.mem_ofSimplex_obj (basePoint p he)⟩)) where
  map : Δ[n + 1] ⟶ E
  map_p : map ≫ p = s.map
  δ_succ (i : Fin (n + 1)) :
    standardSimplex.map (SimplexCategory.δ i.succ) ≫ map = const e
  δ_zero : standardSimplex.map (SimplexCategory.δ 0) ≫ map =
    t.map ≫ (Subcomplex.fiber p b).ι

section

variable (he) {n : ℕ}

lemma exists_deltaStruct [Fibration p] (s : Subcomplex.RelativeMorphism
    (subcomplexBoundary (n + 1)) _
      (const ⟨b, Subcomplex.mem_ofSimplex_obj b⟩)) :
    ∃ (t : Subcomplex.RelativeMorphism
      (subcomplexBoundary n) _
        (const ⟨_, Subcomplex.mem_ofSimplex_obj (basePoint p he)⟩)),
          Nonempty (DeltaStruct s t) := sorry


noncomputable def δ' [Fibration p] (s : Subcomplex.RelativeMorphism
    (subcomplexBoundary (n + 1)) _
      (const ⟨b, Subcomplex.mem_ofSimplex_obj b⟩)) :
    Subcomplex.RelativeMorphism
      (subcomplexBoundary n) _
        (const ⟨_, Subcomplex.mem_ofSimplex_obj (basePoint p he)⟩) :=
  (exists_deltaStruct he s).choose

noncomputable def deltaStruct [Fibration p] (s : Subcomplex.RelativeMorphism
    (subcomplexBoundary (n + 1)) _
      (const ⟨b, Subcomplex.mem_ofSimplex_obj b⟩)) :
    DeltaStruct s (δ' he s) :=
  (exists_deltaStruct he s).choose_spec.some

end

noncomputable def δ (n : ℕ) [Fibration p] [IsFibrant E] [IsFibrant B] :
    π (n + 1) B b → π n (Subcomplex.fiber p b) (basePoint p he) :=
  Quot.lift (fun s ↦ (δ' he s).homotopyClass) sorry

end HomotopySequence

end KanComplex

end SSet
