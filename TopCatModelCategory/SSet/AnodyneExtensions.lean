import TopCatModelCategory.SSet.StrictSegal
import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.SSet.ChosenFiniteProducts
import TopCatModelCategory.SSet.SimplexCategory
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

def standardSimplex.objMk₁ {n : ℕ} (i : Fin (n + 2)) : Δ[1] _[n] :=
  objMk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        by_cases hi : j₁.castSucc < i
        · simp [if_pos hi]
        · rw [if_neg hi, if_neg (fun hj' ↦ hi (lt_of_le_of_lt (by simpa using h) hj'))] }

namespace anodyneExtensions

lemma of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    anodyneExtensions f :=
  MorphismProperty.of_isIso _ _

lemma subcomplexHorn_ι_mem (n : ℕ) (i : Fin (n + 1)) :
    anodyneExtensions (subcomplexHorn.{u} n i).ι := by
  apply MorphismProperty.le_rlp_llp
  simp only [J, MorphismProperty.iSup_iff]
  exact ⟨n, ⟨i⟩⟩

namespace subcomplex_unionProd_face_ι_mem

variable {n : ℕ}

def simplex (i : Fin (n + 1)) :
    (Δ[1] ⊗ Δ[n] : SSet.{u}) _[n + 1] :=
  ⟨standardSimplex.objMk₁ ⟨i + 1, by omega⟩,
    (standardSimplex.objEquiv _ _).symm (SimplexCategory.σ i)⟩

def simplex₀ (i : Fin (n + 1)) (j : Fin (n + 2)) : Fin 2 × Fin (n + 1) :=
  ⟨if j.castSucc < ⟨i + 1, by omega⟩ then 0 else 1, Fin.predAbove i j⟩

lemma injective_simplex₀ (i : Fin (n + 1)) :
    Function.Injective (simplex₀ i) := by
  intro j₁ j₂ h₁
  have h₂ := congr_arg Prod.fst h₁
  have h₃ := congr_arg Prod.snd h₁
  dsimp [simplex₀] at h₂ h₃
  split_ifs at h₂ with h₄ h₅ h₅
  · rw [Fin.predAbove_of_lt_succ _ _ h₄, Fin.predAbove_of_lt_succ _ _ h₅] at h₃
    rwa [Fin.ext_iff] at h₃ ⊢
  · simp at h₂
  · simp at h₂
  · simp only [not_lt] at h₄ h₅
    rwa [Fin.predAbove_of_succ_le _ _ h₄,
      Fin.predAbove_of_succ_le _ _ h₅, Fin.pred_inj] at h₃

noncomputable abbrev ιSimplex (i : Fin (n + 1)) : (Δ[n + 1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[n] :=
  (SSet.yonedaEquiv _ _ ).symm (simplex i)

lemma injective_ιSimplex_app_zero (i : Fin (n + 1)) :
    Function.Injective ((ιSimplex.{u} i).app (op [0])) := by
  intro j₁ j₂ h
  obtain ⟨j₁, rfl⟩ := standardSimplex.obj₀Equiv.symm.surjective j₁
  obtain ⟨j₂, rfl⟩ := standardSimplex.obj₀Equiv.symm.surjective j₂
  apply standardSimplex.obj₀Equiv.injective
  exact injective_simplex₀ i
    (DFunLike.congr_arg (standardSimplex.obj₀Equiv.prodCongr standardSimplex.obj₀Equiv) h)

instance (i : Fin (n + 1)) : Mono (ιSimplex.{u} i) := by
  rw [standardSimplex.mono_iff]
  apply injective_ιSimplex_app_zero

noncomputable def filtration₁ (i : Fin (n + 2)) :
    (Δ[1] ⊗ Δ[n] : SSet.{u}).Subcomplex :=
  Subcomplex.unionProd (standardSimplex.face {1}) (subcomplexBoundary n) ⊔
    (⨆ (j : Fin i.1), Subcomplex.ofSimplex (simplex ⟨j.1, by omega⟩))

variable (n) in
lemma filtration₁_zero :
    filtration₁.{u} (0 : Fin (n + 2)) =
      Subcomplex.unionProd (standardSimplex.face {1}) (subcomplexBoundary n) := by
  simp [filtration₁]

lemma filtration₁_succ (i : Fin (n + 1)) :
    filtration₁.{u} i.succ = filtration₁ i.castSucc ⊔
      Subcomplex.ofSimplex (simplex ⟨i.1, by omega⟩) := by
  dsimp [filtration₁]
  apply le_antisymm
  · simp only [Fin.isValue, sup_le_iff, iSup_le_iff]
    refine ⟨le_sup_left.trans le_sup_left, fun ⟨j, hj⟩ ↦ ?_⟩
    obtain hj | rfl := (Nat.le_of_lt_succ hj).lt_or_eq
    · refine le_trans (le_trans ?_ le_sup_right) le_sup_left
      exact le_iSup (fun (k : Fin i.1) ↦
        Subcomplex.ofSimplex.{u} (simplex (⟨k.1, by omega⟩ : Fin (n + 1)))) ⟨j, hj⟩
    · exact le_sup_right
  · simp only [Fin.isValue, sup_le_iff, le_sup_left, iSup_le_iff, true_and]
    refine ⟨fun ⟨j, hj⟩ ↦ ?_, ?_⟩
    · refine le_trans ?_ le_sup_right
      exact le_iSup (fun (k : Fin (i.1 + 1)) ↦
        Subcomplex.ofSimplex.{u} (simplex (⟨k.1, by omega⟩ : Fin (n + 1)))) ⟨j, by omega⟩
    · refine le_trans ?_ le_sup_right
      exact le_iSup (fun (k : Fin (i.1 + 1)) ↦
        Subcomplex.ofSimplex.{u} (simplex (⟨k.1, by omega⟩ : Fin (n + 1)))) ⟨i, by omega⟩

lemma monotone_filtration₁ : Monotone (filtration₁.{u} (n := n)) := by
  rw [Fin.monotone_iff]
  rintro i
  rw [filtration₁_succ]
  exact le_sup_left

variable (n) in
lemma filtration₁_last :
    filtration₁.{u} (Fin.last (n + 1)) = ⊤ := by
  sorry

lemma preimage_ιSimplex (i : Fin (n + 1)) :
    (filtration₁ i.castSucc).preimage (ιSimplex i) =
      subcomplexHorn.{u} (n + 1) i.succ := by
  sorry

lemma filtration₁_to_succ_mem (i : Fin (n + 1)) :
    anodyneExtensions (Subcomplex.homOfLE (monotone_filtration₁.{u} i.castSucc_le_succ)) := by
  have := IsPushout.of_isColimit
    (Subcomplex.isColimitPushoutCoconeOfPullback (ιSimplex i) (filtration₁.{u} i.castSucc)
      (filtration₁.{u} i.succ) (subcomplexHorn.{u} (n + 1) i.succ) ⊤
      (by simpa using (preimage_ιSimplex i).symm)
      (by simp only [Subcomplex.image_top, filtration₁_succ, Subcomplex.ofSimplex]))
  exact MorphismProperty.of_isPushout (P := anodyneExtensions) this
    (anodyneExtensions.{u}.comp_mem _ _
      (subcomplexHorn_ι_mem (n + 1) i.succ) (of_isIso ((Subcomplex.topIso _).inv)))

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
  · exact mem₀.{u} n
  · exact mem₁.{u} n

lemma subcomplex_unionProd_face_ι_mem {X : SSet.{u}} (Y : X.Subcomplex) (i : Fin 2) :
    anodyneExtensions (Subcomplex.unionProd.{u} (standardSimplex.face {i})
      (subcomplexBoundary n)).ι := by
  sorry -- use `subcomplex_unionProd_face_ι_mem` and the skeleton filtration

lemma subcomplex_unionProd_mem_of_left {X Y : SSet.{u}}
    (A : X.Subcomplex) (B : Y.Subcomplex) (hA : anodyneExtensions A.ι):
    anodyneExtensions (A.unionProd B).ι := by
  sorry

lemma subcomplex_unionProd_mem_of_right {X Y : SSet.{u}}
    (A : X.Subcomplex) (B : Y.Subcomplex) (hB : anodyneExtensions B.ι):
    anodyneExtensions (A.unionProd B).ι := by
  refine (anodyneExtensions.arrow_mk_iso_iff ?_).2
    (subcomplex_unionProd_mem_of_left B A hB)
  sorry

end anodyneExtensions
