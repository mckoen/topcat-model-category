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

noncomputable abbrev simplex (i : Fin (n + 1)) :=
  prodStandardSimplex.nonDegenerateEquiv₁ i

noncomputable abbrev ιSimplex (i : Fin (n + 1)) :
    (Δ[n + 1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[n] :=
  (SSet.yonedaEquiv _ _ ).symm (simplex i)

instance (i : Fin (n + 1)) : Mono (ιSimplex.{u} i) := by
  rw [standardSimplex.mono_iff]
  exact (prodStandardSimplex.objEquiv_non_degenerate_iff' _).1
    (prodStandardSimplex.nonDegenerateEquiv₁.{u} i).2

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

lemma filtration₁_inter_ofSimplex (j : Fin (n + 1)) :
    filtration₁.{u} j.castSucc ⊓ Subcomplex.ofSimplex (simplex.{u} j).1 =
      (subcomplexHorn.{u} (n + 1) j.succ).image (ιSimplex j) := by
  dsimp [filtration₁]
  simp only [Subpresheaf.max_min, Subpresheaf.iSup_min,
    SSet.subcomplexHorn_eq_iSup, Subcomplex.image_iSup]
  sorry

lemma preimage_ιSimplex (j : Fin (n + 1)) :
    (filtration₁ j.castSucc).preimage (ιSimplex j) =
      subcomplexHorn.{u} (n + 1) j.succ := by
  dsimp [filtration₁]
  rw [Subcomplex.preimage_eq_iff]
  apply filtration₁_inter_ofSimplex

lemma filtration₁_to_succ_mem (i : Fin (n + 1)) :
    anodyneExtensions (Subcomplex.homOfLE (monotone_filtration₁.{u} i.castSucc_le_succ)) := by
  have := IsPushout.of_isColimit
    (Subcomplex.isColimitPushoutCoconeOfPullback (ιSimplex i) (filtration₁.{u} i.castSucc)
      (filtration₁.{u} i.succ) (subcomplexHorn.{u} (n + 1) i.succ) ⊤
      (by simpa using (preimage_ιSimplex i).symm)
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
