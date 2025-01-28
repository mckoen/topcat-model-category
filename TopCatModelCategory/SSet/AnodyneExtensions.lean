import TopCatModelCategory.SSet.Horn
import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.SSet.ChosenFiniteProducts
import TopCatModelCategory.SSet.SimplexCategory
import TopCatModelCategory.SSet.NonDegenerateProdSimplex
import TopCatModelCategory.IsFibrant
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

open HomotopicalAlgebra CategoryTheory Limits SSet.ModelCategory MonoidalCategory
  Simplicial Opposite

universe u

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category C] (W : MorphismProperty C) [W.IsMultiplicative]

lemma map_mem_of_fin {n : ℕ} (F : Fin (n + 1) ⥤ C)
    (hF : ∀ (i : Fin n), W (F.map (homOfLE (i.castSucc_le_succ))))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    W (F.map f) := by
  let P (k : ℕ) := ∀ (i j : ℕ) (hj : j < n + 1) (hj' : i + k = j),
    W (F.map (homOfLE ((by simpa only [← hj'] using Nat.le_add_right i k) :
      ⟨i, lt_of_le_of_lt ((Nat.le_add_right i k).trans hj'.le) hj⟩ ≤ ⟨j, hj⟩)))
  suffices ∀ k, P k by
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    have h : i ≤ j := leOfHom f
    obtain ⟨k, hk⟩ := Nat.le.dest h
    exact this k i j (by omega) hk
  intro k
  induction k with
  | zero =>
      intro j j' h h'
      obtain rfl : j = j' := by simpa using h'
      simp only [homOfLE_refl, Functor.map_id]
      apply id_mem
  | succ k hk =>
      intro i j hj hj'
      rw [← homOfLE_comp (x := (⟨i, by omega⟩ : Fin (n + 1)))
        (y := ⟨i + k, by omega⟩) (z := ⟨j, by omega⟩) (Nat.le_add_right i k)
          (by simp only [Fin.le_def]; omega), F.map_comp]
      apply comp_mem
      · exact hk i (i + k) (by omega) rfl
      · rw [← add_assoc] at hj'
        subst hj'
        exact hF ⟨i + k, by omega⟩

end MorphismProperty

end CategoryTheory

namespace SSet

def anodyneExtensions : MorphismProperty SSet.{u} :=
  (fibrations _).llp

instance : anodyneExtensions.{u}.IsMultiplicative := by
  dsimp [anodyneExtensions]
  infer_instance

instance : anodyneExtensions.{u}.RespectsIso := by
  dsimp [anodyneExtensions]
  infer_instance

instance : anodyneExtensions.{u}.IsStableUnderCobaseChange := by
  dsimp [anodyneExtensions]
  infer_instance

namespace anodyneExtensions

lemma hasLeftLiftingProperty {A B : SSet.{u}} {f : A ⟶ B} (hf : anodyneExtensions f)
    ⦃X Y : SSet.{u}⦄ (p : X ⟶ Y) [Fibration p] :
    HasLiftingProperty f p :=
  hf _ (mem_fibrations p)

lemma exists_lift_of_isFibrant {A B X : SSet.{u}} (f : A ⟶ X) [IsFibrant X] {g : A ⟶ B}
    (hg : anodyneExtensions g) :
    ∃ (h : B ⟶ X), g ≫ h = f := by
  have := hg.hasLeftLiftingProperty
  have sq : CommSq f g (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq.lift, by simp⟩

lemma of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    anodyneExtensions f :=
  MorphismProperty.of_isIso _ _

lemma subcomplexHorn_ι_mem (n : ℕ) (i : Fin (n + 2)) :
    anodyneExtensions (subcomplexHorn.{u} (n + 1) i).ι := by
  apply MorphismProperty.le_rlp_llp
  simp only [J, MorphismProperty.iSup_iff]
  exact ⟨n, ⟨i⟩⟩

namespace subcomplex_unionProd_face_ι_mem

noncomputable abbrev simplex (j : Fin (n + 1)) :=
  prodStandardSimplex.nonDegenerateEquiv₁ j

noncomputable abbrev ιSimplex (j : Fin (n + 1)) :
    (Δ[n + 1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[n] :=
  (SSet.yonedaEquiv _ _ ).symm (simplex j)

noncomputable def simplexδ (j : Fin (n + 1)) (i : Fin (n + 2)) :
    (Δ[1] ⊗ Δ[n] : SSet.{u}) _[n] :=
  (Δ[1] ⊗ Δ[n]).δ i (simplex.{u} j)

lemma simplexδ_mem_ofSimplex (j : Fin (n + 1)) (i : Fin (n + 2)) :
    simplexδ.{u} j i ∈ (Subcomplex.ofSimplex (simplex j).1).obj _ :=
  ⟨_, rfl⟩

lemma simplex_δ_zero_snd_mem_subcomplexBoundary (i : Fin (n + 2)) (hi : i ≠ 0) :
    (simplexδ 0 i.succ).2 ∈ (subcomplexBoundary _).obj _ := by
  simp only [subcomplexBoundary_eq_iSup, Subpresheaf.iSup_obj, Set.iSup_eq_iUnion, Set.mem_iUnion,
    standardSimplex.mem_face_iff, Finset.mem_compl, Finset.mem_singleton]
  exact ⟨i, fun k hk ↦ Fin.succAbove_ne _ _ ((SimplexCategory.congr_toOrderHom_apply
    (SimplexCategory.δ_comp_σ_of_gt (n := n) (i := i) (j := 0)
      (Fin.pos_iff_ne_zero.2 hi)).symm k).trans hk)⟩

lemma simplexδ_snd_mem_subcomplexBoundary_of_lt (j : Fin (n + 1)) (i : Fin (n + 3))
    (hij : i < j.succ.castSucc) :
    (simplexδ j.succ i).2 ∈ (subcomplexBoundary _).obj _ := by
  simp only [subcomplexBoundary_eq_iSup, Subpresheaf.iSup_obj, Set.iSup_eq_iUnion, Set.mem_iUnion,
    standardSimplex.mem_face_iff, Finset.mem_compl, Finset.mem_singleton]
  have hi : i ≠ Fin.last _ :=
    fun hi ↦ not_lt_of_ge (j.succ.castSucc.le_last) (by simpa only [hi] using hij)
  rw [← Fin.succ_castSucc, ← Fin.le_castSucc_iff] at hij
  exact ⟨i.castPred hi, fun k hk ↦ Fin.succAbove_ne _ _ ((SimplexCategory.congr_toOrderHom_apply
    (SimplexCategory.δ_comp_σ_of_le (n := n) (i := i.castPred hi) (j := j) hij) k).symm.trans hk)⟩

lemma simplexδ_succ_succ_castSucc (j : Fin (n + 1)) :
    simplexδ j.succ j.succ.castSucc = simplexδ j.castSucc j.succ.castSucc := by
  apply Prod.ext
  · ext k : 1
    simp [simplexδ, simplex, SimplicialObject.δ, standardSimplex.map_op_apply,
      standardSimplex.objMk₁, SimplexCategory.δ]
    by_cases h₁ : j.succ ≤ k
    · simp only [j.succ.castSucc.succAbove_of_le_castSucc k (by simpa)]
      rw [if_neg (by simpa), if_neg (by simpa using j.castSucc_le_succ.trans h₁)]
    · simp only [not_le] at h₁
      simp only [j.succ.castSucc.succAbove_of_succ_le k (by simpa)]
      rw [if_pos (by simpa using h₁.le), if_pos (by simpa [Fin.le_castSucc_iff])]
  · ext k : 1
    exact SimplexCategory.congr_toOrderHom_apply
      ((SimplexCategory.δ_comp_σ_self (i := j.succ)).trans
      (SimplexCategory.δ_comp_σ_succ (i := j.castSucc)).symm) k

@[simp]
lemma ιSimplex_app_objEquiv_symm_δ (j : Fin (n + 1)) (i : Fin (n + 2)) :
    (ιSimplex.{u} j).app (op [n])
      ((standardSimplex.objEquiv [n + 1] (op [n])).symm (SimplexCategory.δ i)) =
      simplexδ j i := by
  rfl

instance (j : Fin (n + 1)) : Mono (ιSimplex.{u} j) := by
  rw [standardSimplex.mono_iff]
  exact (prodStandardSimplex.objEquiv_non_degenerate_iff' _).1
    (prodStandardSimplex.nonDegenerateEquiv₁.{u} j).2

noncomputable def filtration₁ (i : Fin (n + 2)) :
    (Δ[1] ⊗ Δ[n] : SSet.{u}).Subcomplex :=
  Subcomplex.unionProd (standardSimplex.face {1}) (subcomplexBoundary n) ⊔
    (⨆ (j : Fin i.1), Subcomplex.ofSimplex (simplex ⟨j, by omega⟩).1)

variable (n) in
lemma filtration₁_zero :
    filtration₁.{u} (0 : Fin (n + 2)) =
      Subcomplex.unionProd (standardSimplex.face {1}) (subcomplexBoundary n) := by
  simp [filtration₁]

lemma filtration₁_succ (i : Fin (n + 1)) :
    filtration₁.{u} i.succ = filtration₁ i.castSucc ⊔
      Subcomplex.ofSimplex (simplex i).1 := by
  dsimp [filtration₁]
  apply le_antisymm
  · simp only [Fin.isValue, sup_le_iff, iSup_le_iff]
    refine ⟨le_sup_left.trans le_sup_left, fun ⟨j, hj⟩ ↦ ?_⟩
    obtain hj | rfl := (Nat.le_of_lt_succ hj).lt_or_eq
    · refine le_trans (le_trans ?_ le_sup_right) le_sup_left
      dsimp
      exact le_iSup (fun (j : Fin i.1) ↦
        Subcomplex.ofSimplex (simplex ⟨j, by omega⟩).1) ⟨j, hj⟩
    · exact le_sup_right
  · simp only [Fin.isValue, sup_le_iff, le_sup_left, iSup_le_iff, true_and]
    refine ⟨fun ⟨j, hj⟩ ↦ ?_, ?_⟩
    · refine le_trans ?_ le_sup_right
      exact le_iSup (fun (k : Fin (i.1 + 1)) ↦
        Subcomplex.ofSimplex (simplex ⟨k, by omega⟩).1) ⟨j, by omega⟩
    · refine le_trans ?_ le_sup_right
      exact le_iSup (fun (k : Fin (i.1 + 1)) ↦
        Subcomplex.ofSimplex (simplex ⟨k, by omega⟩).1) ⟨i, by omega⟩

lemma monotone_filtration₁ : Monotone (filtration₁.{u} (n := n)) := by
  rw [Fin.monotone_iff]
  rintro i
  rw [filtration₁_succ]
  exact le_sup_left

variable (n) in
lemma filtration₁_last :
    filtration₁.{u} (Fin.last (n + 1)) = ⊤ := by
  rw [prodStandardSimplex.subcomplex_eq_top_iff _ (add_comm 1 n)]
  intro x hx
  obtain ⟨i, hi⟩ := prodStandardSimplex.nonDegenerateEquiv₁.surjective ⟨x, hx⟩
  obtain rfl : simplex i = x := by simp [simplex, hi]
  rw [filtration₁, ← Subcomplex.ofSimplex_le_iff]
  exact (le_iSup (fun (j : Fin (Fin.last (n + 1)).1) ↦
    Subcomplex.ofSimplex (simplex ⟨j, by omega⟩).1) i).trans le_sup_right

lemma le_filtration₁_preimage_ιSimplex (j : Fin (n + 1)) :
    subcomplexHorn.{u} (n + 1) j.succ ≤
    (filtration₁ j.castSucc).preimage (ιSimplex j) := by
  rw [subcomplexHorn_eq_iSup]
  simp only [iSup_le_iff, Subtype.forall, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro i hij
  simp only [standardSimplex.face_singleton_compl, filtration₁,
    Subcomplex.ofSimplex_le_iff, Subcomplex.preimage_obj, Set.mem_preimage,
    Subpresheaf.max_obj, Set.mem_union, Subpresheaf.iSup_obj, Set.iSup_eq_iUnion,
    Set.mem_iUnion]
  rw [ιSimplex_app_objEquiv_symm_δ]
  simp only [Subcomplex.mem_unionProd_iff, standardSimplex.mem_face_iff,
    Finset.mem_singleton]
  dsimp
  by_cases hj₀ : j = 0
  · subst hj₀
    simp only [Fin.succ_zero_eq_one] at hij
    by_cases hi₀ : i = 0
    · subst hi₀
      exact Or.inl (Or.inl (fun i ↦ rfl))
    · refine Or.inl (Or.inr ?_)
      obtain _ | n := n
      · fin_cases i <;> aesop
      obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hi₀
      exact simplex_δ_zero_snd_mem_subcomplexBoundary _ (by rintro rfl; simp at hij)
  · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj₀; clear hj₀
    obtain _ | n := n
    · fin_cases j
    obtain hij | rfl | hij := lt_trichotomy i j.succ.succ
    · rw [← Fin.le_castSucc_iff] at hij
      obtain hij | rfl :=  hij.lt_or_eq
      · exact Or.inl (Or.inr (simplexδ_snd_mem_subcomplexBoundary_of_lt _ _ hij))
      · exact Or.inr ⟨⟨j, by simp⟩,
          by simpa only [simplexδ_succ_succ_castSucc]
            using simplexδ_mem_ofSimplex j.castSucc j.succ.castSucc⟩
    · simp at hij
    · sorry

lemma filtration₁_preimage_ιSimplex_le (j : Fin (n + 1)) :
    (filtration₁ j.castSucc).preimage (ιSimplex j) ≤
      subcomplexHorn.{u} (n + 1) j.succ := by
  dsimp [filtration₁]
  sorry

lemma filtration₁_preimage_ιSimplex (j : Fin (n + 1)) :
    (filtration₁ j.castSucc).preimage (ιSimplex j) =
      subcomplexHorn.{u} (n + 1) j.succ :=
  le_antisymm (filtration₁_preimage_ιSimplex_le j)
    (le_filtration₁_preimage_ιSimplex j)

lemma filtration₁_to_succ_mem (i : Fin (n + 1)) :
    anodyneExtensions (Subcomplex.homOfLE (monotone_filtration₁.{u} i.castSucc_le_succ)) := by
  have := IsPushout.of_isColimit
    (Subcomplex.isColimitPushoutCoconeOfPullback (ιSimplex i) (filtration₁.{u} i.castSucc)
      (filtration₁.{u} i.succ) (subcomplexHorn.{u} (n + 1) i.succ) ⊤
      (by simpa using (filtration₁_preimage_ιSimplex i).symm)
      (by simp only [Subcomplex.image_top, filtration₁_succ, Subcomplex.ofSimplex]))
  exact MorphismProperty.of_isPushout (P := anodyneExtensions) this
    (anodyneExtensions.{u}.comp_mem _ _
      (subcomplexHorn_ι_mem n i.succ) (of_isIso ((Subcomplex.topIso _).inv)))

lemma filtation₁_map_mem {i j : Fin (n + 2)} (h : i ≤ j) :
    anodyneExtensions (Subcomplex.homOfLE (monotone_filtration₁.{u} h)) :=
  anodyneExtensions.map_mem_of_fin
    ((monotone_filtration₁.{u} (n := n)).functor ⋙ Subcomplex.forget _) filtration₁_to_succ_mem
      (homOfLE h)

variable (n) in
lemma mem₁ :
    anodyneExtensions (Subcomplex.unionProd.{u} (standardSimplex.face {(1 : Fin 2)})
      (subcomplexBoundary n)).ι := by
  change anodyneExtensions
    ((Subcomplex.isoOfEq (filtration₁_zero.{u} n)).inv ≫
          (Subcomplex.homOfLE (monotone_filtration₁.{u} (by simp))) ≫
          (Subcomplex.isoOfEq (filtration₁_last.{u} n)).hom ≫
          (Subcomplex.topIso _).hom)
  refine anodyneExtensions.comp_mem _ _ ?_
    (anodyneExtensions.comp_mem _ _ (filtation₁_map_mem (by simp))
    (anodyneExtensions.comp_mem _ _ ?_ ?_))
  all_goals apply of_isIso

variable (n) in
lemma mem₀ :
    anodyneExtensions (Subcomplex.unionProd.{u} (standardSimplex.face {(0 : Fin 2)})
      (subcomplexBoundary n)).ι := by
  sorry -- same as `mem₁`, but inserting the simplices in reverse order

end subcomplex_unionProd_face_ι_mem

open subcomplex_unionProd_face_ι_mem in
lemma subcomplex_unionProd_face_boundary_ι_mem (n : ℕ) (i : Fin 2) :
    anodyneExtensions (Subcomplex.unionProd.{u} (standardSimplex.face {i})
      (subcomplexBoundary n)).ι := by
  fin_cases i
  · exact mem₀ n
  · exact mem₁ n

lemma subcomplex_unionProd_mem_of_left {X Y : SSet.{u}}
    (A : X.Subcomplex) (B : Y.Subcomplex) (hA : anodyneExtensions A.ι) :
    anodyneExtensions (A.unionProd B).ι := by
  sorry

lemma subcomplex_unionProd_mem_of_right {X Y : SSet.{u}}
    (A : X.Subcomplex) (B : Y.Subcomplex) (hB : anodyneExtensions B.ι) :
    anodyneExtensions (A.unionProd B).ι :=
  (anodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (Subcomplex.unionProd.symmIso _ _) (β_ _ _))).2
    (subcomplex_unionProd_mem_of_left B A hB)

end anodyneExtensions

end SSet
