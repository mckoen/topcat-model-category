import TopCatModelCategory.SSet.NonDegenerateProdSimplex

open CategoryTheory Simplicial MonoidalCategory SSet

variable {n : ℕ}

@[simp]
def f₂' (a b : Fin n) : Fin (n + 1) → Fin 3 :=
  fun k ↦
    if k ≤ a.castSucc then 0
    else if k ≤ b.succ then 1
    else 2

/-- `[n] → [2]`. `0 ≤ a ≤ b < n` -/
def f₂ (a b : Fin n) : Fin (n + 1) →o Fin 3 where
  toFun := f₂' a b
  monotone' := by
    refine Fin.monotone_iff_le_succ.mpr ?_
    intro i
    dsimp
    split
    · next => omega
    · next h =>
      have h' : ¬i < a := fun h' ↦ h h'.le
      simp [h']
      split
      · next => aesop
      · next h =>
        split
        next h' =>
          exfalso
          apply h
          rw [Fin.le_iff_val_le_val]
          dsimp
          omega
        next => omega

open SimplexCategory stdSimplex in
/-- `0 ≤ a ≤ b < n` -/
noncomputable
def f (a b : Fin (n + 1)) : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (objEquiv.symm (σ a), objMk (f₂ a b))

open SimplexCategory stdSimplex in
/-- `0 ≤ a ≤ b ≤ n` -/
noncomputable
def g (a b : Fin (n + 2)) : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (objEquiv.symm (σ a.castSucc ≫ σ b), objMk (f₂ a b))

open Subcomplex in
noncomputable
def σ (a b : Fin (n + 1)) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  range (f a b)

open Subcomplex in
noncomputable
def τ (a b : Fin (n + 2)) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  range (g a b)

open stdSimplex

open SimplexCategory in
instance (a b : Fin (n + 1)) : Mono (f a b) := by
  rw [mono_iff]
  intro ⟨(g :  ⦋0⦌ ⟶ ⦋n + 1⦌)⟩ ⟨(h : ⦋0⦌ ⟶ ⦋n + 1⦌)⟩
  intro H
  ext e
  simp [f, SSet.yonedaEquiv, yonedaCompUliftFunctorEquiv, stdSimplex] at H
  change
    ((SSet.uliftFunctor.obj (yoneda ^⦋n⦌)).map _ _, (SSet.uliftFunctor.obj (yoneda ^⦋2⦌)).map _ _) =
    ((SSet.uliftFunctor.obj (yoneda ^⦋n⦌)).map _ _, (SSet.uliftFunctor.obj (yoneda ^⦋2⦌)).map _ _) at H
  simp [ChosenFiniteProducts.product, yoneda, SSet.uliftFunctor] at H
  obtain ⟨H, H'⟩ := H
  refine Fin.val_eq_of_eq ?_
  change g.toOrderHom e = h.toOrderHom e
  simp [Hom.toOrderHom]
  apply_fun (fun f ↦ f.toOrderHom e) at H
  simp [SimplexCategory.σ, objEquiv, Hom.toOrderHom, Hom.mk, Equiv.ulift, CategoryStruct.comp,
    OrderHom.comp] at H
  apply_fun (fun f ↦ f.toOrderHom e) at H'
  simp [Hom.toOrderHom, objMk, f₂, objEquiv,
    Equiv.ulift, Hom.mk, CategoryStruct.comp, OrderHom.comp] at H'
  by_cases a.castSucc < g.toOrderHom e
  all_goals rename_i h'
  · simp [Hom.toOrderHom] at h'
    simp [Fin.predAbove, h', h'.not_le] at H H'
    aesop
  · simp only [len_mk, Nat.reduceAdd, not_lt] at h'
    simp [Hom.toOrderHom] at h'
    simp [Fin.predAbove, h', h'.not_lt] at H H'
    by_cases a.castSucc < h.toOrderHom e
    all_goals rename_i h''
    · simp [Hom.toOrderHom] at h''
      simp [h'', h''.not_le] at H H'
      aesop
    · simp only [len_mk, Nat.reduceAdd, not_lt] at h''
      simp [Hom.toOrderHom] at h''
      simp only [h''.not_lt, reduceDIte] at H
      rw [Fin.castPred_eq_iff_eq_castSucc] at H
      aesop

open SimplexCategory in
/-- only works for `0 ≤ a ≤ b ≤ n` -/
instance (a b : Fin (n + 1)) (hab : a ≤ b) : Mono (g a.castSucc b.castSucc) := by
  rw [mono_iff]
  dsimp [g]
  rw [← prodStdSimplex.nonDegenerate_iff', prodStdSimplex.nonDegenerate_iff _ rfl]
  ext i
  simp [f₂, SimplexCategory.σ]
  rw [← stdSimplex.map_objEquiv_symm, map_objEquiv_symm_apply]
  cases i using Fin.lastCases with
  | last =>
    simp
    split
    next h =>
      simp_all only [Fin.isValue, Fin.val_zero, OfNat.zero_ne_ofNat]
      rw [Fin.eq_mk_iff_val_eq] at h
      simp only [Fin.coe_castSucc, Fin.val_last] at h
      omega
    next h =>
      split
      next h_1 =>
        simp_all only [Fin.isValue, Fin.val_one, OfNat.one_ne_ofNat]
        rw [Fin.eq_mk_iff_val_eq] at h_1
        simp only [Fin.coe_castSucc, Fin.val_last] at h_1
        omega
      next h_1 => simp_all only [Fin.isValue, Fin.val_two]
  | cast i =>
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      simp [Fin.predAbove]
      split
      next h =>
        simp_all
        split
        next h_1 =>
          simp_all only [Fin.coe_pred, Fin.coe_castSucc, Fin.isValue]
          split
          next
            h_2 => omega
          next h_2 =>
            simp_all only [not_lt, Fin.isValue]
            split
            next h_2 =>
              simp_all only [Fin.isValue, Fin.val_one, add_left_inj]
              exfalso
              rw [Fin.le_iff_val_le_val] at h_2
              simp only [Fin.coe_castSucc, Fin.val_succ, add_le_add_iff_right,
                Fin.val_fin_le] at h_2
              omega
            next h_2 => omega
        next h_1 =>
          simp_all only [not_lt, Fin.isValue, add_right_inj]
          split
          next h_2 => omega
          next h_2 =>
            simp_all only [not_lt, Fin.isValue]
            split
            next h_2 => simp_all only [Fin.isValue, Fin.val_one]
            next h_2 =>
              simp_all only [not_le, Fin.isValue, Fin.val_two, OfNat.ofNat_ne_one]
              apply h_2.not_le
              rw [Fin.le_iff_val_le_val] at h_1 ⊢
              aesop
      next h =>
        simp_all
        split
        next => omega
        next => aesop
