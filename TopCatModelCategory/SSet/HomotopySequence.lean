--import TopCatModelCategory.SSet.Homotopy
import TopCatModelCategory.SSet.Fiber
import TopCatModelCategory.SSet.HomotopyGroup

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

def map₁ (n : ℕ) : π n (Subcomplex.fiber p b) (basePoint p he) → π n E e :=
  mapπ (Subcomplex.fiber p b).ι n (basePoint p he) e (by simp)

def map₂ (n : ℕ) : π n E e → π n B b := mapπ p n e b he

variable {p he}

structure DeltaStruct {n : ℕ}
    (s : B.PtSimplex (n + 1) b)
    (t : PtSimplex _ n (basePoint p he)) where
  map : Δ[n + 1] ⟶ E
  map_p : map ≫ p = s.map
  δ_succ (i : Fin (n + 1)) :
    standardSimplex.map (SimplexCategory.δ i.succ) ≫ map = const e
  δ_zero : standardSimplex.map (SimplexCategory.δ 0) ≫ map =
    t.map ≫ (Subcomplex.fiber p b).ι

section

variable (he) {n : ℕ}

lemma exists_deltaStruct [Fibration p] (s : B.PtSimplex (n + 1) b) :
    ∃ (t : PtSimplex _ n (basePoint p he)),
          Nonempty (DeltaStruct s t) := by
  have sq : CommSq (const e) (subcomplexHorn (n + 1) 0).ι p s.map := ⟨by
    have := Subcomplex.homOfLE (subcomplexHorn_le_subcomplexBoundary (0 : Fin (n + 2))) ≫=
      s.comm
    simp only [Subcomplex.homOfLE_ι_assoc, Subcomplex.ofSimplex_ι] at this
    rw [this, const_comp, comp_const, comp_const, he]⟩
  refine ⟨⟨Subcomplex.lift
      (standardSimplex.map (SimplexCategory.δ 0) ≫ sq.lift) ?_, ?_⟩, ⟨{
    map := sq.lift
    map_p := by simp
    δ_succ i := subcomplexHorn.ι (i := 0) (j := i.succ) i.succ_ne_zero ≫= sq.fac_left
    δ_zero := by rfl }⟩⟩
  · apply le_antisymm (by simp)
    rw [← Subcomplex.image_le_iff, Subcomplex.image_top,
      Subcomplex.range_le_fiber_iff,
      Category.assoc, sq.fac_right, PtSimplex.δ_map]
  · rw [← cancel_mono (Subpresheaf.ι _),
      Subcomplex.ofSimplex_ι, comp_const, const_comp, Subpresheaf.ι_app, basePoint_coe,
      Category.assoc, Subcomplex.lift_ι]
    obtain _ | n := n
    · ext x hx
      simp at hx
      exact ((Set.mem_empty_iff_false _).1 hx.2).elim
    · apply subcomplexBoundary.hom_ext
      intro i
      rw [subcomplexBoundary.ι_ι_assoc, ← Functor.map_comp_assoc, comp_const]
      have := SimplexCategory.δ_comp_δ (n := n) (i := 0) (j := i) (by simp)
      dsimp at this
      rw [← this, Functor.map_comp_assoc]
      have := subcomplexHorn.ι.{u} 0 i.succ i.succ_ne_zero ≫= sq.fac_left
      rw [subcomplexHorn.ι_ι_assoc] at this
      rw [this, comp_const, comp_const]

noncomputable def δ' [Fibration p] (s : B.PtSimplex (n + 1) b) :
    PtSimplex _ n (basePoint p he) :=
  (exists_deltaStruct he s).choose

noncomputable def deltaStruct [Fibration p] (s : B.PtSimplex (n + 1) b) :
    DeltaStruct s (δ' he s) :=
  (exists_deltaStruct he s).choose_spec.some

end

noncomputable def δ (n : ℕ) [Fibration p] [IsFibrant E] [IsFibrant B] :
    π (n + 1) B b → π n (Subcomplex.fiber p b) (basePoint p he) :=
  Quot.lift (fun s ↦ (δ' he s).homotopyClass) sorry

end HomotopySequence

end KanComplex

end SSet
