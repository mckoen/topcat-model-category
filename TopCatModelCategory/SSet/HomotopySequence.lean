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

structure DeltaStruct {n : ℕ} (s : B.PtSimplex (n + 1) b)
    (t : PtSimplex _ n (basePoint p he)) (i : Fin (n + 2)) where
  map : Δ[n + 1] ⟶ E
  map_p : map ≫ p = s.map
  δ_map : standardSimplex.map (SimplexCategory.δ i) ≫ map =
    t.map ≫ (Subcomplex.fiber p b).ι
  δ_map_eq_const (j : Fin (n + 2)) (hi : j ≠ i) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const e

section

variable (he) {n : ℕ}

lemma exists_deltaStruct [Fibration p] (s : B.PtSimplex (n + 1) b) (i : Fin (n + 2)) :
    ∃ (t : PtSimplex _ n (basePoint p he)),
          Nonempty (DeltaStruct s t i) := by
  have sq : CommSq (const e) (subcomplexHorn (n + 1) i).ι p s.map := ⟨by
    have := Subcomplex.homOfLE (subcomplexHorn_le_subcomplexBoundary i) ≫=
      s.comm
    simp only [Subcomplex.homOfLE_ι_assoc, Subcomplex.ofSimplex_ι] at this
    rw [this, const_comp, comp_const, comp_const, he]⟩
  refine ⟨⟨Subcomplex.lift
      (standardSimplex.map (SimplexCategory.δ i) ≫ sq.lift) ?_, ?_⟩, ⟨{
    map := sq.lift
    map_p := by simp
    δ_map := rfl
    δ_map_eq_const j hj := subcomplexHorn.ι _ _ hj ≫= sq.fac_left }⟩⟩
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
      intro j
      rw [subcomplexBoundary.ι_ι_assoc, ← Functor.map_comp_assoc, comp_const]
      have fac (k : Fin (n + 3)) (hk : k ≠ i) := subcomplexHorn.ι i k hk ≫= sq.fac_left
      simp only [comp_const, subcomplexHorn.ι_ι_assoc] at fac
      obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
      · have := SimplexCategory.δ_comp_δ (n := n) (i := 0) (j := j) (by simp)
        dsimp at this
        rw [← this, Functor.map_comp_assoc, fac _ (by simp [Fin.ext_iff]), comp_const]
      · by_cases hj : j ≤ i
        · rw [SimplexCategory.δ_comp_δ hj, Functor.map_comp_assoc,
            fac, comp_const]
          rintro h
          rw [← Fin.succ_le_succ_iff, ← h] at hj
          simp at hj
        · simp only [not_le] at hj
          obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
          simp only [Fin.succ_castSucc]
          rw [← SimplexCategory.δ_comp_δ hj, Functor.map_comp_assoc, fac, comp_const]
          simp only [ne_eq, Fin.succ_inj]
          rintro rfl
          simp at hj

noncomputable def δ'' [Fibration p] (s : B.PtSimplex (n + 1) b) (i : Fin (n + 2)):
    PtSimplex _ n (basePoint p he) :=
  (exists_deltaStruct he s i).choose

noncomputable def deltaStruct [Fibration p] (s : B.PtSimplex (n + 1) b) (i : Fin (n + 2)) :
    DeltaStruct s (δ'' he s i) i :=
  (exists_deltaStruct he s i).choose_spec.some

variable {he} in
def uniqueδ'' [Fibration p] {s s' : B.PtSimplex (n + 1) b} {i : Fin (n + 2)}
    {t t' : PtSimplex _ n (basePoint p he)} (hst : DeltaStruct s t i) (hst' : DeltaStruct s' t' i)
    (hs : s.Homotopy s') :
    t.Homotopy t' := sorry

end

noncomputable def δ' (n : ℕ) [Fibration p] [IsFibrant E] [IsFibrant B] (i : Fin (n + 2)) :
    π (n + 1) B b → π n (Subcomplex.fiber p b) (basePoint p he) :=
  Quot.lift (fun s ↦ (δ'' he s i).homotopyClass) (fun s s' hs ↦
    Quot.sound ⟨uniqueδ'' (deltaStruct he s i) (deltaStruct he s' i) hs.some⟩)

end HomotopySequence

end KanComplex

end SSet
