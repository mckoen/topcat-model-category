import TopCatModelCategory.SSet.Fiber
import TopCatModelCategory.SSet.HomotopyGroup

universe u

open HomotopicalAlgebra CategoryTheory Simplicial SSet.modelCategoryQuillen

namespace SSet

namespace KanComplex

namespace HomotopySequence

variable {E B : SSet.{u}} (p : E ⟶ B) {b : B _⦋0⦌}
  {e : E _⦋0⦌} (he : p.app _ e = b)

@[simps]
def basePoint : (Subcomplex.fiber p b : SSet) _⦋0⦌ :=
  ⟨e, by simpa [Subcomplex.fiber]⟩

def map₁ (n : ℕ) : π n (Subcomplex.fiber p b) (basePoint p he) → π n E e :=
  mapπ (Subcomplex.fiber p b).ι n (basePoint p he) e (by simp)

def map₂ (n : ℕ) : π n E e → π n B b := mapπ p n e b he

variable {p he}

structure DeltaStruct {n : ℕ} (s : B.PtSimplex (n + 1) b)
    (t : PtSimplex _ n (basePoint p he)) (i : Fin (n + 2)) where
  map : Δ[n + 1] ⟶ E
  map_p : map ≫ p = s.map := by aesop_cat
  δ_map : stdSimplex.map (SimplexCategory.δ i) ≫ map =
    t.map ≫ (Subcomplex.fiber p b).ι := by aesop_cat
  δ_map_eq_const (j : Fin (n + 2)) (hi : j ≠ i) :
    stdSimplex.map (SimplexCategory.δ j) ≫ map = const e := by aesop_cat

namespace DeltaStruct

attribute [reassoc (attr := simp)] map_p δ_map
attribute [reassoc] δ_map_eq_const

def relStructOfCastSucc {n : ℕ} {s : B.PtSimplex (n + 1) b}
    {t : PtSimplex _ n (basePoint p he)} {i : Fin (n + 1)}
    (h : DeltaStruct s t i.castSucc) :
      PtSimplex.RelStruct (t.pushforward (Subpresheaf.ι _) e (by simp)) .const i where
  map := h.map
  δ_succ_map := h.δ_map_eq_const _ (by simp [Fin.ext_iff])
  δ_map_of_lt j hj := h.δ_map_eq_const j hj.ne
  δ_map_of_gt j hj := h.δ_map_eq_const j (by
    rintro rfl
    simp [Fin.lt_iff_val_lt_val] at hj)

def relStructOfSucc {n : ℕ} {s : B.PtSimplex (n + 1) b}
    {t : PtSimplex _ n (basePoint p he)} {i : Fin (n + 1)}
    (h : DeltaStruct s t i.succ) :
      PtSimplex.RelStruct .const (t.pushforward (Subpresheaf.ι _) e (by simp))  i where
  map := h.map
  δ_succ_map := by simp
  δ_castSucc_map := h.δ_map_eq_const _ (by simp [Fin.ext_iff])
  δ_map_of_lt j hj := h.δ_map_eq_const j (by
    rintro rfl
    simp [Fin.lt_iff_val_lt_val] at hj)
  δ_map_of_gt j hj := h.δ_map_eq_const j hj.ne'

noncomputable def relStruct₀ {n : ℕ} {s : B.PtSimplex (n + 1) b}
    {t : PtSimplex _ n (basePoint p he)} {i : Fin (n + 2)} [IsFibrant E]
    (h : DeltaStruct s t i) :
      PtSimplex.RelStruct₀ (t.pushforward (Subpresheaf.ι _) e (by simp)) .const := by
  apply Nonempty.some
  obtain ⟨i, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
  · exact ⟨(relStructOfCastSucc h).relStruct₀⟩
  · exact ⟨(relStructOfSucc (i := Fin.last n) h).relStruct₀.symm⟩

end DeltaStruct

section

variable (he) {n : ℕ}

lemma exists_deltaStruct [Fibration p] (s : B.PtSimplex (n + 1) b) (i : Fin (n + 2)) :
    ∃ (t : PtSimplex _ n (basePoint p he)),
          Nonempty (DeltaStruct s t i) := by
  have sq : CommSq (const e) (horn (n + 1) i).ι p s.map := ⟨by
    have := Subcomplex.homOfLE (horn_le_boundary i) ≫=
      s.comm
    simp only [Subcomplex.homOfLE_ι_assoc, Subcomplex.ofSimplex_ι] at this
    rw [this, const_comp, comp_const, comp_const, he]⟩
  refine ⟨⟨Subcomplex.lift
      (stdSimplex.map (SimplexCategory.δ i) ≫ sq.lift) ?_, ?_⟩, ⟨{
    map := sq.lift
    map_p := by simp
    δ_map := rfl
    δ_map_eq_const j hj := horn.ι _ _ hj ≫= sq.fac_left }⟩⟩
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
    · apply boundary.hom_ext
      intro j
      rw [boundary.ι_ι_assoc, ← Functor.map_comp_assoc, comp_const]
      have fac (k : Fin (n + 3)) (hk : k ≠ i) := horn.ι i k hk ≫= sq.fac_left
      simp only [comp_const, horn.ι_ι_assoc] at fac
      obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
      · have := SimplexCategory.δ_comp_δ (n := n) (i := 0) (j := j) (by simp)
        dsimp at this
        rw [← this, Functor.map_comp_assoc, fac _ (fun h ↦ by
          rw [Fin.ext_iff] at h
          simp at h), comp_const]
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

variable (p he n) in
noncomputable def δ' (n : ℕ) [Fibration p] [IsFibrant E] [IsFibrant B] (i : Fin (n + 2)) :
    π (n + 1) B b → π n (Subcomplex.fiber p b) (basePoint p he) :=
  Quot.lift (fun s ↦ (δ'' he s i).homotopyClass) (fun s s' hs ↦
    Quot.sound ⟨uniqueδ'' (deltaStruct he s i) (deltaStruct he s' i) hs.some⟩)

lemma δ'_mk_eq_of_deltaStruct {n : ℕ} [Fibration p] [IsFibrant E] [IsFibrant B]
    {i : Fin (n + 2)} {x : B.PtSimplex (n + 1) b}
    {t : SSet.PtSimplex (Subcomplex.fiber p b) n (basePoint p he)}
    (h : DeltaStruct x t i) :
    δ' p he n i (π.mk x) = π.mk t :=
  Quot.sound ⟨uniqueδ'' (deltaStruct he x i) h (.refl x)⟩

variable [IsFibrant B]

@[simp]
lemma map₂_map₁_apply {n : ℕ} (x : π n (Subcomplex.fiber p b) (basePoint p he)) :
    map₂ p he n (map₁ p he n x) = 1 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  dsimp only [map₁, map₂]
  rw [mapπ_mapπ, mapπ_mk, π.mk_eq_one_iff]
  refine ⟨PtSimplex.RelStruct₀.ofEq ?_⟩
  ext : 1
  dsimp
  rw [Subcomplex.fiber_ι_comp, comp_const]

variable [Fibration p] [IsFibrant E]

@[simp]
lemma δ'_map₂_apply {n : ℕ} (x : π (n + 1) E e) (i : Fin (n + 2)) :
    δ' p he n i (map₂ p he (n + 1) x) = 1 := by
  obtain ⟨s, rfl⟩ := x.mk_surjective
  exact δ'_mk_eq_of_deltaStruct { map := s.map }

@[simp]
lemma map₁_δ'_apply {n : ℕ} (x : π (n + 1) B b) (i : Fin (n + 2)) :
    map₁ p he n (δ' p he n i x) = 1 := by
  obtain ⟨s, rfl⟩ := x.mk_surjective
  dsimp [map₁]
  have h := deltaStruct he s i
  rw [δ'_mk_eq_of_deltaStruct h, mapπ_mk, π.mk_eq_one_iff]
  exact ⟨h.relStruct₀⟩

end HomotopySequence

end KanComplex

end SSet
