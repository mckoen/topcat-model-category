import TopCatModelCategory.SSet.AnodyneExtensionsDefs

open HomotopicalAlgebra CategoryTheory Limits SSet.modelCategory MonoidalCategory
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

namespace anodyneExtensions

namespace subcomplex_unionProd_face_ι_mem

variable {n : ℕ}

noncomputable abbrev simplex (j : Fin (n + 1)) :=
  prodStdSimplex.nonDegenerateEquiv₁ j

noncomputable abbrev ιSimplex (j : Fin (n + 1)) :
    (Δ[n + 1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[n] :=
  SSet.yonedaEquiv.symm (simplex j)

noncomputable def simplexδ (j : Fin (n + 1)) (i : Fin (n + 2)) :
    (Δ[1] ⊗ Δ[n] : SSet.{u}) _⦋n⦌ :=
  (Δ[1] ⊗ Δ[n]).δ i (simplex.{u} j)

lemma simplexδ_mem_ofSimplex (j : Fin (n + 1)) (i : Fin (n + 2)) :
    simplexδ.{u} j i ∈ (Subcomplex.ofSimplex (simplex j).1).obj _ :=
  ⟨_, rfl⟩

lemma simplexδ_snd_mem_boundary_of_gt (j : Fin (n + 1)) (i : Fin (n + 3))
    (hij : i < j.succ.castSucc) :
    (simplexδ j.succ i).2 ∈ (boundary _).obj _ := by
  simp only [boundary_eq_iSup, Subpresheaf.iSup_obj, Set.iSup_eq_iUnion, Set.mem_iUnion,
    stdSimplex.mem_face_iff, Finset.mem_compl, Finset.mem_singleton]
  have hi : i ≠ Fin.last _ :=
    fun hi ↦ not_lt_of_ge (j.succ.castSucc.le_last) (by simpa only [hi] using hij)
  rw [← Fin.succ_castSucc, ← Fin.le_castSucc_iff] at hij
  exact ⟨i.castPred hi, fun k hk ↦ Fin.succAbove_ne _ _ ((SimplexCategory.congr_toOrderHom_apply
    (SimplexCategory.δ_comp_σ_of_le (n := n) (i := i.castPred hi) (j := j) hij) k).symm.trans hk)⟩

lemma simplexδ_snd_mem_boundary_of_lt (j i : Fin (n + 2))
    (hij : j < i) :
    (simplexδ j i.succ).2 ∈ (boundary _).obj _ := by
  simp only [boundary_eq_iSup, Subpresheaf.iSup_obj, Set.iSup_eq_iUnion, Set.mem_iUnion,
    stdSimplex.mem_face_iff, Finset.mem_compl, Finset.mem_singleton]
  have hj : j ≠ Fin.last _ := by
    rintro rfl
    exact (Fin.le_last i).not_lt hij
  exact ⟨i, fun k hk ↦
    Fin.succAbove_ne _ _ ((SimplexCategory.congr_toOrderHom_apply
      (SimplexCategory.δ_comp_σ_of_gt (n := n) (i := i) (j := j.castPred hj)
        (by simpa using hij)) k).symm.trans hk)⟩

lemma simplexδ_succ_succ_castSucc (j : Fin (n + 1)) :
    simplexδ j.succ j.succ.castSucc = simplexδ j.castSucc j.succ.castSucc := by
  apply Prod.ext
  · ext k : 1
    simp [simplexδ, simplex, SimplicialObject.δ, stdSimplex.map_op_apply,
      stdSimplex.objMk₁, SimplexCategory.δ]
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

lemma simplexδ_succ_snd (j : Fin (n + 1)) :
    (simplexδ j j.succ).2 = stdSimplex.objMk .id :=
  stdSimplex.objEquiv.injective SimplexCategory.δ_comp_σ_succ

lemma ιSimplex_app_objEquiv_symm_δ (j : Fin (n + 1)) (i : Fin (n + 2)) :
    (ιSimplex.{u} j).app (op ⦋n⦌)
      (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) =
      simplexδ j i := by
  rfl

instance (j : Fin (n + 1)) : Mono (ιSimplex.{u} j) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.non_degenerate_iff' _).1
    (prodStdSimplex.nonDegenerateEquiv₁.{u} j).2

noncomputable def filtration₁ (i : Fin (n + 2)) :
    (Δ[1] ⊗ Δ[n] : SSet.{u}).Subcomplex :=
  Subcomplex.unionProd (stdSimplex.face {1}) (boundary n) ⊔
    (⨆ (j : Fin i.1), Subcomplex.ofSimplex (simplex ⟨j, by omega⟩).1)

variable (n) in
lemma filtration₁_zero :
    filtration₁.{u} (0 : Fin (n + 2)) =
      Subcomplex.unionProd (stdSimplex.face {1}) (boundary n) := by
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
  rw [prodStdSimplex.subcomplex_eq_top_iff _ (add_comm 1 n)]
  intro x hx
  obtain ⟨i, hi⟩ := prodStdSimplex.nonDegenerateEquiv₁.surjective ⟨x, hx⟩
  obtain rfl : simplex i = x := by simp [simplex, hi]
  rw [filtration₁, ← Subcomplex.ofSimplex_le_iff]
  exact (le_iSup (fun (j : Fin (Fin.last (n + 1)).1) ↦
    Subcomplex.ofSimplex (simplex ⟨j, by omega⟩).1) i).trans le_sup_right

lemma le_filtration₁_preimage_ιSimplex (j : Fin (n + 1)) :
    horn.{u} (n + 1) j.succ ≤
    (filtration₁ j.castSucc).preimage (ιSimplex j) := by
  rw [horn_eq_iSup]
  simp only [iSup_le_iff, Subtype.forall, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro i hij
  simp only [stdSimplex.face_singleton_compl, filtration₁,
    Subcomplex.ofSimplex_le_iff, Subcomplex.preimage_obj, Set.mem_preimage,
    Subpresheaf.max_obj, Set.mem_union, Subpresheaf.iSup_obj, Set.iSup_eq_iUnion,
    Set.mem_iUnion]
  rw [ιSimplex_app_objEquiv_symm_δ]
  simp only [Subcomplex.mem_unionProd_iff, stdSimplex.mem_face_iff,
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
      apply simplexδ_snd_mem_boundary_of_lt
      by_contra!
      simp at this
      simp [this] at hij
  · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj₀; clear hj₀
    obtain _ | n := n
    · fin_cases j
    obtain hij | rfl | hij := lt_trichotomy i j.succ.succ
    · rw [← Fin.le_castSucc_iff] at hij
      obtain hij | rfl :=  hij.lt_or_eq
      · exact Or.inl (Or.inr (simplexδ_snd_mem_boundary_of_gt _ _ hij))
      · exact Or.inr ⟨⟨j, by simp⟩,
          by simpa only [simplexδ_succ_succ_castSucc]
            using simplexδ_mem_ofSimplex j.castSucc j.succ.castSucc⟩
    · simp at hij
    · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) (by rintro rfl; simp at hij)
      refine Or.inl (Or.inr
        (simplexδ_snd_mem_boundary_of_lt _ _ (by simpa using hij)))

lemma Set.not_mem_setOf {α : Type*} (P : α → Prop) (x : α) :
    x ∉ setOf P ↔ ¬ P x := by simp only [Set.nmem_setOf_iff]

lemma filtration₁_preimage_ιSimplex_le (j : Fin (n + 1)) :
    (filtration₁ j.castSucc).preimage (ιSimplex j) ≤
      horn.{u} (n + 1) j.succ := by
  simp only [stdSimplex.subcomplex_le_horn_iff,
    stdSimplex.face_singleton_compl, ← Subcomplex.image_le_iff,
    Subcomplex.image_ofSimplex, Subcomplex.ofSimplex_le_iff]
  rw [ιSimplex_app_objEquiv_symm_δ]
  simp [filtration₁, Subcomplex.unionProd, Set.prod, Set.not_mem_setOf]
  refine ⟨⟨?_, ⟨j, ?_⟩⟩, fun i ↦ ?_⟩
  · simpa only [simplexδ_succ_snd] using non_mem_boundary n
  · simp [simplexδ, SimplicialObject.δ, stdSimplex.map_op_apply,
      stdSimplex.objMk₁, SimplexCategory.δ]
  · rw [prodStdSimplex.mem_ofSimplex_iff, Set.not_subset]
    refine ⟨⟨0, j⟩, ⟨j, ?_⟩, ?_⟩
    · ext : 1
      · simp [simplexδ, SimplicialObject.δ, stdSimplex.objMk₁,
          SimplexCategory.δ]
      · simp [simplexδ_succ_snd]
        rfl
    · obtain ⟨i, hi⟩ := i
      rintro ⟨⟨a, ha₀⟩, ha⟩
      simp [simplex, Prod.ext_iff, stdSimplex.objMk₁] at ha
      obtain ⟨ha₁, ha₂⟩ := ha
      change Fin.predAbove _ _ = _ at ha₂
      rw [Fin.predAbove_of_le_castSucc _ _ (by simp; omega), Fin.ext_iff] at ha₂
      dsimp at ha₂
      omega

lemma filtration₁_preimage_ιSimplex (j : Fin (n + 1)) :
    (filtration₁ j.castSucc).preimage (ιSimplex j) =
      horn.{u} (n + 1) j.succ :=
  le_antisymm (filtration₁_preimage_ιSimplex_le j)
    (le_filtration₁_preimage_ιSimplex j)

lemma filtration₁_to_succ_mem (i : Fin (n + 1)) :
    anodyneExtensions (Subcomplex.homOfLE (monotone_filtration₁.{u} i.castSucc_le_succ)) := by
  have := IsPushout.of_isColimit
    (Subcomplex.isColimitPushoutCoconeOfPullback (ιSimplex i) (filtration₁.{u} i.castSucc)
      (filtration₁.{u} i.succ) (horn.{u} (n + 1) i.succ) ⊤
      (by simpa using (filtration₁_preimage_ιSimplex i).symm)
      (by
        simp only [Subcomplex.image_top,
          filtration₁_succ, Subcomplex.ofSimplex_eq_range]))
  exact MorphismProperty.of_isPushout (P := anodyneExtensions) this
    (anodyneExtensions.{u}.comp_mem _ _
      (horn_ι_mem n i.succ) (of_isIso ((Subcomplex.topIso _).inv)))

lemma filtation₁_map_mem {i j : Fin (n + 2)} (h : i ≤ j) :
    anodyneExtensions (Subcomplex.homOfLE (monotone_filtration₁.{u} h)) :=
  anodyneExtensions.map_mem_of_fin
    ((monotone_filtration₁.{u} (n := n)).functor ⋙ Subcomplex.forget _) filtration₁_to_succ_mem
      (homOfLE h)

variable (n) in
lemma mem₁ :
    anodyneExtensions (Subcomplex.unionProd.{u} (stdSimplex.face {(1 : Fin 2)})
      (boundary n)).ι := by
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
    anodyneExtensions (Subcomplex.unionProd.{u} (stdSimplex.face {(0 : Fin 2)})
      (boundary n)).ι := by
  sorry -- same as `mem₁`, but inserting the simplices in reverse order

end subcomplex_unionProd_face_ι_mem

open subcomplex_unionProd_face_ι_mem in
lemma subcomplex_unionProd_face_boundary_ι_mem (n : ℕ) (i : Fin 2) :
    anodyneExtensions (Subcomplex.unionProd.{u} (stdSimplex.face {i})
      (boundary n)).ι := by
  fin_cases i
  · exact mem₀ n
  · exact mem₁ n

end anodyneExtensions

end SSet
