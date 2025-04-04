
import TopCatModelCategory.SSet.Horn
import TopCatModelCategory.SSet.DimensionProd
import TopCatModelCategory.SSet.NonDegenerateProdSimplex
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

universe u

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

variable (n : ℕ)

/-- `[n + 2] → [n]`, defined for each `0 ≤ a ≤ b ≤ n`. -/
def g₁ {n} (a b : Fin (n + 1)) : Fin (n + 3) →o Fin (n + 1) where
  toFun := (Fin.predAbove a) ∘ (Fin.predAbove b.succ) -- should be right
  monotone' := (Fin.predAbove_right_monotone _).comp (Fin.predAbove_right_monotone _)

@[simp]
def f₂' {n} (a b : Fin (n + 1)) : Fin (n + 2) → Fin 3 :=
  fun k ↦
    if k ≤ a.castSucc then 0
    else if k ≤ b.succ then 1
    else 2

/-- `[n + 1 + 1] → [2]`. `0 ≤ a ≤ b < n` -/
def f₂ {n} (a b : Fin (n + 1)) (hab : a ≤ b) : Fin (n + 2) →o Fin 3 where
  toFun := f₂' a b
  monotone' := by
    refine Fin.monotone_iff_le_succ.mpr ?_
    intro i
    rcases i with ⟨i, hi⟩
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    by_cases i ≤ a
    · aesop
    · rename_i h
      by_cases i ≤ b + 1
      · rename_i h'
        simp [h, h']
        by_cases (i + 1 ≤ a)
        · linarith
        · rename_i h''
          simp [h'']
          aesop
      · rename_i h'
        have p : ¬(i + 1 ≤ a) := by linarith
        have q : ¬(i ≤ b) := by linarith
        simp [h, h', p, q]

/-- `[n + 2] → [2]`. -/
abbrev g₂ {n} (a b : Fin (n + 2)) (hab : a ≤ b) : Fin (n + 3) →o Fin 3 := f₂ a b (by simp [hab])

open stdSimplex

open SimplexCategory in
noncomputable
def f {n} (a b : Fin (n + 1)) (hab : a ≤ b) : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] :=
  ((Δ[n] ⊗ Δ[2]).yonedaEquiv).symm ⟨⟨σ a⟩, objMk (f₂ a b hab)⟩

open SimplexCategory in
noncomputable
def g {n} (a b : Fin (n + 2)) (hab : a ≤ b) : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  ((Δ[n] ⊗ Δ[2]).yonedaEquiv).symm ⟨objMk (g₁ a b), objMk (g₂ a b hab)⟩

open Subcomplex in
noncomputable
def σ {n} (a b : Fin (n + 1)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  ofSimplex <| (Δ[n] ⊗ Δ[2]).yonedaEquiv (f a b hab)

open Subpresheaf in
lemma σeq {n} (a b : Fin (n + 1)) (hab : a ≤ b) : σ a b hab = Subpresheaf.range (f a b hab) := by
  dsimp [σ]
  rw [← Subcomplex.range_eq_ofSimplex]

open Subcomplex in
noncomputable
def τ {n} (a b : Fin (n + 2)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  ofSimplex <| (Δ[n] ⊗ Δ[2]).yonedaEquiv (g a b hab)

open SimplexCategory in
instance (a b : Fin (n + 1)) (hab : a ≤ b) : Mono (f a b hab) := by
  rw [stdSimplex.mono_iff]
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
  simp [SimplexCategory.σ, Hom.toOrderHom, Hom.mk, CategoryStruct.comp,
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
instance (a b : Fin (n + 2)) (hab : a ≤ b) : Mono (g a b hab) := by
  rw [mono_iff]
  intro ⟨(g' :  ⦋0⦌ ⟶ ⦋n + 2⦌)⟩ ⟨(h : ⦋0⦌ ⟶ ⦋n + 2⦌)⟩
  intro H
  ext e
  simp [g, SSet.yonedaEquiv, yonedaCompUliftFunctorEquiv, stdSimplex] at H
  change
    ((SSet.uliftFunctor.obj (yoneda ^⦋n⦌)).map _ _, (SSet.uliftFunctor.obj (yoneda ^⦋2⦌)).map _ _) =
    ((SSet.uliftFunctor.obj (yoneda ^⦋n⦌)).map _ _, (SSet.uliftFunctor.obj (yoneda ^⦋2⦌)).map _ _) at H
  simp [ChosenFiniteProducts.product, yoneda, SSet.uliftFunctor] at H
  obtain ⟨H, H'⟩ := H
  refine Fin.val_eq_of_eq ?_
  change g'.toOrderHom e = h.toOrderHom e
  simp [Hom.toOrderHom]
  apply_fun (fun f ↦ f.toOrderHom e) at H
  simp [g₁] at H
  simp [SimplexCategory.σ, Hom.toOrderHom, Hom.mk, CategoryStruct.comp,
    OrderHom.comp] at H
  apply_fun (fun f ↦ f.toOrderHom e) at H'
  simp [Hom.toOrderHom, objMk, g₂, objEquiv,
    Equiv.ulift, Hom.mk, CategoryStruct.comp, OrderHom.comp, f₂] at H H'

  by_cases a.castSucc < g'.toOrderHom e
  all_goals rename_i h'
  · simp [Hom.toOrderHom] at h'
    simp [Fin.predAbove, h', h'.not_le] at H'
    by_cases a.castSucc < h.toOrderHom e
    all_goals rename_i h''
    · simp [Hom.toOrderHom] at h''
      simp [h'', h''.not_le] at H'
      simp [Fin.predAbove] at H
      by_cases (b : Fin (n + 1)).succ.castSucc < g'.toOrderHom e
      all_goals rename_i h'''
      · simp [Hom.toOrderHom] at h'''
        simp [h''', h'''.not_le] at H H'
        have : ¬(g'.toOrderHom e ≤ b.succ) := by
          simp
          have := h'''
          simp [Hom.toOrderHom]
          have : (b : Fin (n + 1)).succ.castSucc = b.succ := by
            simp [Fin.castSucc, Fin.succ]
            sorry
          sorry

        sorry
      · simp at h'''
        simp [Hom.toOrderHom] at h'''
        simp [h'''.not_lt, h'''] at H H'
        have : (b : Fin (n + 1)).succ.castSucc = b.succ := by
          simp [Fin.castSucc, Fin.succ]

          sorry

        sorry
    · simp at h''
      simp [Hom.toOrderHom] at h''
      aesop
  · simp only [len_mk, Nat.reduceAdd, not_lt] at h'
    simp [Hom.toOrderHom] at h'
    simp [Fin.predAbove, h', h'.not_lt] at H H'
    sorry

/-- `Y(b)` for `0 ≤ b ≤ n`. Goes up to `Y(n)`, the first object in the `τ` filtration. -/
-- `Y(b) = Y(0) ⊔ [σ00] ⊔ [σ01 ⊔ σ11] ⊔ ... ⊔ [σ0(b-1) ⊔ σ1(b-1) ⊔ ... ⊔ σ(b-1)(b-1)]`
-- ``Y(n) = Y(0) ⊔ [σ00] ⊔ [σ01 ⊔ σ11] ⊔ ... ⊔ [σ0(n-1) ⊔ σ1(n-1) ⊔ ... ⊔ σ(n-1)(n-1)]`
noncomputable
def filtration₁ {n} (b : Fin (n + 1)) :
    (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (Subcomplex.unionProd (boundary n) (horn 2 1)) ⊔
    (⨆ (i : Fin b.1) (k : Fin i.succ.1), -- 0 ≤ k ≤ i ≤ b - 1
      σ ⟨k, lt_of_le_of_lt (Nat.le_of_lt_succ k.2) (i.2.trans b.2)⟩ ⟨i, (i.2.trans b.2)⟩
        (Fin.mk_le_mk.2 (Fin.is_le k)))

lemma filtration₁_zero :
    filtration₁ (0 : Fin (n + 1)) =
      (Subcomplex.unionProd (boundary n) (horn 2 1)) := by
  simp [filtration₁]

/-- `Y(b) ↪ Y(b + 1)` for `b < n` is just the union of `Y(b.castSucc)` with `[σ0b ⊔ ... ⊔ σbb]` -/
-- `Y(n - 1) ↪ Y(n)` is just the union of `Y(n - 1)` with `[σ0(n - 1) ⊔ ... ⊔ σ(n - 1)(n - 1)]`
lemma filtration₁_succ (b : Fin n) :
    filtration₁ b.succ =
      filtration₁ b.castSucc ⊔ -- 0 ≤ i ≤ b, ⨆ σib
        (⨆ (i : Fin b.succ.1), σ ⟨i, i.2.trans b.succ.2⟩ b.castSucc (Fin.le_castSucc_iff.mpr i.2)) := by
    simp [filtration₁]
    apply le_antisymm
    · apply sup_le
      · apply le_sup_of_le_left <| le_sup_of_le_left le_rfl
      · apply iSup₂_le
        intro i k
        by_cases i.1 < b; all_goals rename_i h
        · apply le_sup_of_le_left
          apply le_sup_of_le_right
          apply le_iSup₂_of_le ⟨i, h⟩ k
          rfl
        · have : i.1 = b := by
            rw [not_lt] at h
            refine le_antisymm (Fin.is_le i) h
          apply le_sup_of_le_right
          apply le_iSup_of_le ⟨k, by simp [← this]⟩
          simp [this]
          rfl
    · apply sup_le
      · apply sup_le
        · simp only [le_sup_left]
        · apply le_sup_of_le_right
          apply iSup₂_le
          intro i k
          apply le_iSup₂_of_le ⟨i, Nat.lt_add_right 1 i.2⟩ k
          rfl
      · apply le_sup_of_le_right
        apply iSup_le
        intro i
        apply le_iSup₂_of_le ⟨b, by simp⟩ i
        rfl

-- `Y(b,a) = Y(b) ⊔ ... ⊔ σ (a - 1) b` for `0 ≤ a ≤ b < n`, if k : Fin a.1

-- `Y(b,a) = Y(b) ⊔ ... ⊔ σ a b` for `0 ≤ a ≤ b < n`. if k : Fin.a.succ.1
-- `Y(b,a + 1) = Y(b) ⊔ ... ⊔ σ (a + 1) b`
-- `Y(b,b) = Y(b) ⊔ σ0b ... ⊔ σbb`
-- `Y(n - 1, n - 1) = Y(n - 1) ⊔ σ0(n - 1) ... ⊔ σ(n - 1)(n - 1) = Y(n)`
noncomputable
def filtration₂ {n} (b : Fin n) (a : Fin b.succ.1) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (filtration₁ b) ⊔ (⨆ (k : Fin a.succ.1), σ k b (by
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    rcases k with ⟨k, hk⟩
    dsimp at ha hk ⊢
    refine (Fin.natCast_le_natCast ?_ ?_).mpr ?_
    all_goals linarith))

-- `Y(b,0) = Y(b) ∪ (σ0b)` for `0 ≤ b < n`
-- if we adjust defn above then Y(b,0) = Y(b). not sure which is better
lemma filtration₂_zero (b : Fin n) :
    filtration₂ b ⟨0, Nat.zero_lt_succ b⟩ = filtration₁ b ⊔ (σ 0 b (Fin.zero_le _)) := by
  simp [filtration₂]
  rfl

-- `Y(b,b) = Y(b) ⊔ σ0b ... ⊔ σbb`
-- `Y(b,b) = Y(b + 1)` for `0 ≤ b < n`
-- `Y(0, 0) = Y(0) ⊔ σ00 = Y(1)`
-- `Y(n - 1, n - 1) = Y(n)`
lemma filtration₂_last (b : Fin n) :
    filtration₂ b ⟨b, Nat.lt_add_one b⟩ = filtration₁ b.succ := by
  simp [filtration₂]
  rw [filtration₁_succ]
  apply le_antisymm
  · apply sup_le (le_sup_of_le_left le_rfl)
    apply le_sup_of_le_right
    apply iSup_le
    intro i
    apply le_iSup_of_le i
    have : (i : Fin (n + 1)) = ⟨i, LT.lt.trans i.isLt b.succ.isLt⟩ := by
      refine Fin.eq_mk_iff_val_eq.mpr ?_
      simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      refine i.2.trans (Nat.add_lt_add_right b.2 1)
    simp_rw [this]
    rfl
  · refine sup_le (le_sup_of_le_left le_rfl) (le_sup_of_le_right (iSup_le fun i ↦ ?_))
    apply le_iSup_of_le i
    have : (i : Fin (n + 1)) = ⟨i, LT.lt.trans i.isLt b.succ.isLt⟩ := by
      refine Fin.eq_mk_iff_val_eq.mpr ?_
      simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      refine i.2.trans (Nat.add_lt_add_right b.2 1)
    simp_rw [this]
    rfl

-- for `b < n`, `Y(b) ↪ Y(b + 1)` factors as `Y(b) ↪ Y(b,0) ↪ Y(b,1) ↪ ... ↪ Y(b,b) = Y(b + 1)`
-- e.g. `Y(n - 1) ↪ Y(n)` factors as `Y(n - 1) ↪ Y(n - 1,0) ↪ Y(n - 1,1) ↪ ... ↪ Y(n - 1,n - 1) = Y(n)`

-- `0 ≤ a ≤ b < n`
-- `Y(b,a) = Y(b) ⊔ ... ⊔ σab`
-- `Y(b,a + 1) = Y(b) ⊔ ... ⊔ σ(a + 1)b`
/-- `Y(b,a) ↪ Y(b, a + 1)` for `a < b ≤ n` is just the union of `Y(b,a)` with `σ(a + 1)b`. -/
lemma filtration₂_succ (b : Fin n) (a : Fin b.1) :
    filtration₂ b a.succ = (filtration₂ b a.castSucc) ⊔
      (σ a.succ b (Fin.natCast_mono b.2.le (Fin.is_le a.succ))) := by
  simp [filtration₂]
  apply le_antisymm
  · apply sup_le (le_sup_of_le_left le_sup_left)
    apply iSup_le
    intro ⟨i, hi⟩
    dsimp at hi ⊢
    cases lt_or_eq_of_le (Nat.le_of_lt_succ hi)
    · rename_i h
      apply le_sup_of_le_left
      apply le_sup_of_le_right
      apply le_iSup_of_le ⟨i, h⟩
      rfl
    · rename_i h
      simp_rw [h]
      apply le_sup_of_le_right
      rfl
  · apply sup_le
    · apply sup_le le_sup_left
      apply le_sup_of_le_right
      apply iSup_le
      intro i
      apply le_iSup_of_le ⟨i, Nat.lt_add_right 1 i.2⟩
      rfl
    · apply le_sup_of_le_right
      apply le_iSup_of_le ⟨a + 1, lt_add_one _⟩
      rfl

/-- `X(b)` for `0 ≤ b ≤ n + 1`. Goes up to `X(n + 1)`. -/
-- `X(b) = Y(n) ⊔ [τ00] ⊔ [τ01 ⊔ τ11] ⊔ ... ⊔ [τ0(b-1) ⊔ τ1(b-1) ⊔ ... ⊔ τ(b-1)(b-1)]`
-- `X(n) = Y(n) ⊔ [τ00] ⊔ [τ01 ⊔ τ11] ⊔ ... ⊔ [τ0(n-1) ⊔ τ1(n-1) ⊔ ... ⊔ τ(n-1)(n-1)]`
-- `X(n + 1) = X(n) ⊔ [τ0n ⊔ τ1n ⊔ ... ⊔ τnn]`
noncomputable
def filtration₃ {n} (b : Fin (n + 2)) :
    (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (filtration₁ n) ⊔
    (⨆ (i : Fin b.1) (k : Fin i.succ.1), -- 0 ≤ k ≤ i ≤ b - 1
      τ ⟨k, lt_of_le_of_lt (Nat.le_of_lt_succ k.2) (i.2.trans b.2)⟩ ⟨i, (i.2.trans b.2)⟩
        (Fin.mk_le_mk.2 (Fin.is_le k)))

lemma filtration₃_zero :
    filtration₃ (0 : Fin (n + 2)) = filtration₁ n := by
  simp [filtration₃]

/-- `X(b) ↪ X(b + 1)` for `b ≤ n` is just the union of `X(b.castSucc)` with `[τ0b ⊔ ... ⊔ τbb]` -/
-- `X(n) ↪ X(n + 1)` is just the union of `X(n)` with `[τ0n ⊔ ... ⊔ τnn]`
lemma filtration₃_succ (b : Fin (n + 1)) :
    filtration₃ b.succ =
      filtration₃ b.castSucc ⊔ -- 0 ≤ i ≤ b, ⨆ σib
        (⨆ (i : Fin b.succ.1), τ ⟨i, i.2.trans b.succ.2⟩ b.castSucc (Fin.le_castSucc_iff.mpr i.2)) := by
    simp [filtration₁]
    apply le_antisymm
    · apply sup_le
      · apply le_sup_of_le_left <| le_sup_of_le_left le_rfl
      · apply iSup₂_le
        intro i k
        by_cases i.1 < b; all_goals rename_i h
        · apply le_sup_of_le_left
          apply le_sup_of_le_right
          apply le_iSup₂_of_le ⟨i, h⟩ k
          rfl
        · have : i.1 = b := by
            rw [not_lt] at h
            refine le_antisymm (Fin.is_le i) h
          apply le_sup_of_le_right
          apply le_iSup_of_le ⟨k, by simp [← this]⟩
          simp [this]
          rfl
    · apply sup_le
      · apply sup_le
        · apply le_sup_of_le_left
          rfl
        · apply le_sup_of_le_right
          apply iSup₂_le
          intro i k
          apply le_iSup₂_of_le ⟨i, Nat.lt_add_right 1 i.2⟩ k
          rfl
      · apply le_sup_of_le_right
        apply iSup_le
        intro i
        apply le_iSup₂_of_le ⟨b, by simp⟩ i
        rfl

lemma filtration₃_last : filtration₃ (n.succ) = (⊤ : (Δ[n] ⊗ Δ[2]).Subcomplex) := by
  rw [prodStdSimplex.subcomplex_eq_top_iff _ rfl]
  intro z hz
  --#check prodStandardSimplex.objEquiv_non_degenerate_iff
  --#check standardSimplex.mem_non_degenerate_iff_mono
  -- show that all nondegenerate n+2 simplices are contained in X(n).obj (n + 2). (they are in all the τ's)
  sorry

-- `X(b,a) = X(b) ⊔ ... ⊔ τ a b` for `0 ≤ a ≤ b ≤ n`.
-- `X(b,a + 1) = X(b) ⊔ ... ⊔ τ (a + 1) b`
-- `X(b,b) = X(b) ⊔ τ0b ... ⊔ τbb`
-- `X(n, n) = X(n) ⊔ τ0n ... ⊔ τnn = X(n + 1) = Δ[n] ⊗ Δ[2]`
noncomputable
def filtration₄ {n} (b : Fin (n + 1)) (a : Fin b.succ.1) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (filtration₃ b) ⊔ (⨆ (k : Fin a.succ.1), τ k b (by
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    rcases k with ⟨k, hk⟩
    dsimp at ha hk ⊢
    refine (Fin.natCast_le_natCast ?_ ?_).mpr ?_
    all_goals linarith))

-- `X(b,0) = X(b) ∪ (τ0b)` for `0 ≤ b ≤ n`
lemma filtration₄_zero (b : Fin (n + 1)) :
    filtration₄ b ⟨0, Nat.zero_lt_succ b⟩ = filtration₃ b ⊔ (τ 0 b (Fin.zero_le _)) := by
  simp [filtration₄]
  rfl

-- `X(b,b) = X(b) ⊔ τ0b ... ⊔ τbb`
-- `X(b,b) = X(b + 1)` for `0 ≤ b < n`
-- `X(0, 0) = X(0) ⊔ τ00 = X(1)`
-- `X(n, n) = X(n + 1)`
lemma filtration₄_last (b : Fin (n + 1)) :
    filtration₄ b ⟨b, Nat.lt_add_one b⟩ = filtration₃ b.succ := by
  simp [filtration₄]
  rw [filtration₃_succ]
  apply le_antisymm
  · apply sup_le (le_sup_of_le_left le_rfl)
    apply le_sup_of_le_right
    apply iSup_le
    intro i
    apply le_iSup_of_le i
    have : (i : Fin (n + 2)) = ⟨i, LT.lt.trans i.isLt b.succ.isLt⟩ := by
      refine Fin.eq_mk_iff_val_eq.mpr ?_
      simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      refine i.2.trans (Nat.add_lt_add_right b.2 1)
    simp_rw [this]
    rfl
  · apply sup_le (le_sup_of_le_left le_rfl)
    apply le_sup_of_le_right
    apply iSup_le
    intro i
    apply le_iSup_of_le i
    have : (i : Fin (n + 2)) = ⟨i, LT.lt.trans i.isLt b.succ.isLt⟩ := by
      refine Fin.eq_mk_iff_val_eq.mpr ?_
      simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      refine i.2.trans (Nat.add_lt_add_right b.2 1)
    simp_rw [this]
    rfl

-- `X(b,a) = X(b) ⊔ ... ⊔ τab`
-- `X(b,a + 1) = X(b) ⊔ ... ⊔ τ(a + 1)b`
/-- `X(b,a) ↪ X(b, a + 1)` for `a < b ≤ n + 1` is just the union of `X(b,a)` with `τ(a + 1)b`. -/
lemma filtration₄_succ (b : Fin n) (a : Fin b.1) :
    filtration₂ b a.succ = (filtration₂ b a.castSucc) ⊔
      (σ a.succ b (Fin.natCast_mono b.2.le (Fin.is_le a.succ))) := by
  simp [filtration₂]
  apply le_antisymm
  · apply sup_le (le_sup_of_le_left le_sup_left)
    apply iSup_le
    intro ⟨i, hi⟩
    dsimp at hi ⊢
    cases lt_or_eq_of_le (Nat.le_of_lt_succ hi)
    · rename_i h
      apply le_sup_of_le_left
      apply le_sup_of_le_right
      apply le_iSup_of_le ⟨i, h⟩
      rfl
    · rename_i h
      simp_rw [h]
      apply le_sup_of_le_right
      rfl
  · apply sup_le
    · apply sup_le le_sup_left
      apply le_sup_of_le_right
      apply iSup_le
      intro i
      apply le_iSup_of_le ⟨i, Nat.lt_add_right 1 i.2⟩
      rfl
    · apply le_sup_of_le_right
      apply le_iSup_of_le ⟨a + 1, lt_add_one _⟩
      rfl

lemma filtration₄_last' : filtration₄ n ⟨n, by simp⟩ = (⊤ : (Δ[n] ⊗ Δ[2]).Subcomplex) := by
  have h₁ := filtration₄_last n n
  have h₂ := filtration₃_last n
  simp at h₁ h₂
  rw [h₁, h₂]

-- the image of Λ[n + 1, a + 1] under σab : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]
-- (f a b hab).app k <| (subcomplexHorn (n + 1) (a.succ)).obj k
noncomputable
def hornProdSubcomplex {n} (a b : Fin (n + 1)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  Subcomplex.image (horn (n + 1) (a.succ)) (f a b hab)

noncomputable
def boundaryProdSubcomplex {n} (a b : Fin (n + 1)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  Subcomplex.image (boundary (n + 1)) (f a b hab)

--image of i-th face under some f : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]
noncomputable
def SSet.face' {n} (i : Fin (n + 2)) (f : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  Subcomplex.image (face {i}ᶜ) f

-- image of Λ[n + 1, a + 1] under (f a b hab) is the union of the image under f of all faces except
-- the (a + 1)-th
lemma hornProdSubcomplex_eq_iSup (a b : Fin (n + 1)) (hab : a ≤ b) :
    hornProdSubcomplex a b hab =
      ⨆ (j : ({a.succ}ᶜ : Set (Fin (n + 2)))), face' j.1 (f a b hab) := by
  dsimp [hornProdSubcomplex, face']
  rw [horn_eq_iSup]
  aesop

lemma boundaryProdSubcomplex_eq_iSup (a b : Fin (n + 1)) (hab : a ≤ b) :
    boundaryProdSubcomplex a b hab =
      ⨆ (j : Fin (n + 2)), face' j.1 (f a b hab) := by
  dsimp [boundaryProdSubcomplex, face']
  rw [boundary_eq_iSup]
  aesop

-- Λ[n + 1, a + 1] ≤ σab, so Λ[n + 1, a] ≤ σ(a - 1)b
open Subcomplex in
lemma hornProdSubcomplex_le₁ {n} (a b : Fin (n + 1)) (hab : a ≤ b) :
    hornProdSubcomplex.{u} a b hab ≤ σ a b hab := by
  rw [hornProdSubcomplex_eq_iSup]
  dsimp [face', σ]
  apply iSup_le
  intro ⟨j, hj⟩
  rw [face_singleton_compl, image_ofSimplex, ofSimplex_le_iff,
    prodStdSimplex.mem_ofSimplex_iff]
  intro i
  simp [Set.mem_range]
  intro k h
  exact ⟨_, h⟩

-- each face except the a-th and (a+1)-th is contained in the unionProd
open Subcomplex in
lemma face_le {n} (a b : Fin (n + 1)) (hab : a ≤ b) (j : Fin (n + 2))
    (hj : j ∈ ({a.succ}ᶜ :  Set (Fin (n + 2)))) (h : ¬j = a.castSucc) :
      face' j (f a b hab) ≤ (boundary n).unionProd (horn 2 1) := by
  dsimp [Subcomplex.unionProd, face']
  all_goals rw [face_singleton_compl, image_ofSimplex, ofSimplex_le_iff]
  right --then check every other face
  refine ⟨?_, by simp only [Subpresheaf.top_obj, Set.top_eq_univ, Set.mem_univ]⟩
  change ¬Function.Surjective (a.predAbove ∘ j.succAbove)
  intro h'
  have : j < a.castSucc ∨ a.succ < j := by
    cases Fin.lt_or_lt_of_ne hj
    all_goals cases Fin.lt_or_lt_of_ne h
    · left; assumption
    · rename_i q q'
      exfalso
      apply not_lt.2 q' q
    · left; assumption
    · right; assumption
  cases this
  all_goals rename_i hj'
  · obtain ⟨e, he⟩ := h' ⟨j, lt_trans hj' a.2⟩
    simp at he
    by_cases a.castSucc < (j.succAbove e)
    all_goals rename_i h''
    all_goals simp [Fin.predAbove, h'', Fin.succAbove] at he h''
    all_goals by_cases e.castSucc < j; all_goals rename_i h'''
    all_goals simp [h'''] at h'' he
    all_goals try simp [h''] at he
    · apply_fun (fun f ↦ f.castSucc) at he
      simp at he
      simp [← he] at h'''
      exact (Fin.pred_castSucc_lt (Fin.castSucc_ne_zero_of_lt h'')).le.not_lt h'''
    · rw [he] at h''
      exact h''.not_lt hj'
    · simp [h''.not_lt] at he
      simp [he] at h'''
    · apply_fun (fun f ↦ f.castSucc) at he
      simp [Lean.Omega.Fin.not_le.mpr h''] at he
      rw [← he] at h'''
      aesop
  · obtain ⟨e, he⟩ := h' (j.pred (Fin.ne_zero_of_lt hj'))
    simp at he
    by_cases a.castSucc < (j.succAbove e)
    all_goals rename_i h''
    all_goals simp [Fin.predAbove, h'', Fin.succAbove] at he h''
    all_goals by_cases e.castSucc < j; all_goals rename_i h'''
    all_goals simp [h'''] at h'' he
    all_goals try simp [h''] at he
    · aesop
    · rw [he] at h'''
      exact h''' (Fin.castSucc_pred_lt (Fin.ne_zero_of_lt hj'))
    · rw [← not_lt] at h''
      simp [h''] at he
      rw [he] at h''
      exact h'' ((Fin.lt_pred_iff (Fin.ne_zero_of_lt hj')).mpr hj')
    · apply_fun (fun f ↦ f.castSucc) at he
      simp [Lean.Omega.Fin.not_le.mpr h''] at he
      refine h''' (lt_trans (Fin.castSucc_lt_succ e) ?_)
      rw [he]
      exact Fin.castSucc_pred_lt (Fin.ne_zero_of_lt hj')

-- the 0-th face of σ0b is contained in the unionProd
open Subcomplex in
lemma face_le' {n} (b : Fin (n + 1)):
      face' 0 (f 0 b b.zero_le) ≤ (boundary n).unionProd (horn 2 1) := by
  dsimp [Subcomplex.unionProd, face']
  rw [face_singleton_compl, image_ofSimplex, ofSimplex_le_iff]
  simp
  left
  refine ⟨trivial, ?_⟩
  change Set.range (f₂' 0 b ∘ Fin.succ) ∪ {1} ≠ Set.univ
  intro h'
  rw [Set.eq_univ_iff_forall] at h'
  have h'' := h' 0
  simp at h''
  obtain ⟨e, he⟩ := h''
  have := he e.succ_ne_zero
  aesop

--for a > 0 show a-th face of σab = a-th face of σ(a-1)b
open Subcomplex in
lemma face_eq {n} (a b : Fin (n + 1)) (hab : a ≤ b) (j : Fin (n + 2)) (hj : ¬j = a.succ)
    (h : j = a.castSucc) (ha : ¬a = 0) :
    face'.{u} a.castSucc (f a b hab) =
      face'.{u} a.castSucc (f (a.castSucc.pred (Fin.castSucc_ne_zero_iff.mpr ha)) b
        (by rw [Fin.pred_le_iff]; exact ((Fin.castSucc_le_castSucc_iff.2 hab).trans (Fin.castSucc_le_succ b)))) := by
  dsimp [Subcomplex.unionProd, face']
  rw [face_singleton_compl, image_ofSimplex]
  simp
  congr
  simp [f, SimplexCategory.δ, SimplexCategory.σ]
  change ((SSet.uliftFunctor.obj (yoneda ^⦋n⦌)).map _ _,
    (SSet.uliftFunctor.obj (yoneda ^⦋2⦌)).map _ _) =
    ((SSet.uliftFunctor.obj (yoneda ^⦋n⦌)).map _ _,
    (SSet.uliftFunctor.obj (yoneda ^⦋2⦌)).map _ _)
  simp [yoneda, SSet.uliftFunctor, ChosenFiniteProducts.product]
  refine ⟨?_, ?_⟩
  · have : a.predAbove ∘ a.castSucc.succAbove =
        (a.castSucc.pred (Fin.castSucc_ne_zero_iff.mpr ha)).predAbove ∘ a.castSucc.succAbove := by
      ext e
      simp
      by_cases a ≤ e
      all_goals rename_i h'
      · have := Fin.succAbove_castSucc_of_le _ _ h'
        simp [h', this]
        have := Fin.predAbove_pred_of_le a.castSucc e.succ ?_ (Fin.castSucc_ne_zero_iff.mpr ha)
        simp [this]
        have : a.castSucc ≤ e.castSucc := h'
        exact this.trans e.castSucc_le_succ
      · rw [not_le] at h'
        have := Fin.succAbove_castSucc_of_lt _ _ h'
        simp [h', this]
        have := Fin.predAbove_pred_of_lt a.castSucc e.castSucc h'
        simp only [this, Fin.castPred_castSucc]
    simp [CategoryStruct.comp, SimplexCategory.Hom.mk, SimplexCategory.comp_toOrderHom,
      SimplexCategory.Hom.toOrderHom, objEquiv, Equiv.ulift, OrderEmbedding.toOrderHom,
      Fin.succAboveOrderEmb]
    aesop
  · simp [f₂]
    have : f₂' a b ∘ a.castSucc.succAbove =
        f₂' (a.castSucc.pred (Fin.castSucc_ne_zero_iff.mpr ha)) b ∘ a.castSucc.succAbove := by
      ext e
      by_cases e < a
      all_goals rename_i h'
      · simp [h', Fin.succAbove, h'.le,
          (Fin.le_pred_castSucc_iff (Fin.castSucc_ne_zero_iff.mpr ha)).mpr h']
      · simp [h', Fin.succAbove]
        have : ¬e < a.castSucc.pred (Fin.castSucc_ne_zero_iff.mpr ha) := by
          intro p
          apply h'
          have : a.castSucc.pred (Fin.castSucc_ne_zero_iff.mpr ha) < a := Fin.pred_castSucc_lt (Fin.castSucc_ne_zero_iff.mpr ha)
          exact p.trans this
        by_cases e ≤ b
        all_goals rename_i h''
        all_goals simp [h'', this]
    simp [CategoryStruct.comp, SimplexCategory.Hom.mk, SimplexCategory.comp_toOrderHom,
      SimplexCategory.Hom.toOrderHom, objEquiv, Equiv.ulift, OrderEmbedding.toOrderHom,
      Fin.succAboveOrderEmb, OrderHom.comp, objMk]
    aesop

-- show a-th face of σab ≤ σ(a-1)b
open Subcomplex in
lemma face_le'' {n} (a b : Fin (n + 1)) (hab : a ≤ b) (j : Fin (n + 2))
    (hj : j ∈ ({a.succ}ᶜ : Set (Fin (n + 2)))) (h : j = a.castSucc) (ha : a ≠ 0) :
      face' a.castSucc (f a b hab) ≤ σ (a.castSucc.pred (Fin.castSucc_ne_zero_iff.mpr ha)) b
        ((Fin.pred_castSucc_lt (Fin.castSucc_ne_zero_iff.mpr ha)).le.trans hab) := by
  rw [face_eq a b hab j hj h ha]
  dsimp [face', σ]
  rw [face_singleton_compl, image_ofSimplex, ofSimplex_le_iff,
    prodStdSimplex.mem_ofSimplex_iff]
  intro e
  aesop

-- 0 ≤ a < b < n
-- Λ[n + 1, (a + 1) + 1] ↪ Y(b,a) = Y(b) ⊔ ... ⊔ σ a b
open Subcomplex in
lemma hornProdSubcomplex_le₂ {n} (b : Fin n) (a : Fin b.1) :
    hornProdSubcomplex
      ⟨a.succ, lt_of_le_of_lt a.succ.le_val_last (Nat.lt_add_right 1 (by simp [b.2]))⟩
      ⟨b.1, Nat.lt_add_right 1 b.2⟩ (by simpa using a.succ.le_val_last) ≤
        filtration₂ b a.castSucc := by
  rw [hornProdSubcomplex_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases j = (⟨a.succ, lt_of_le_of_lt a.succ.le_val_last (Nat.lt_add_right 1 (by simp [b.2]))⟩ : Fin (n + 1)).castSucc -- check the a-th face first
  all_goals rename_i h
  · by_cases (⟨a.succ, lt_of_le_of_lt a.succ.le_val_last (Nat.lt_add_right 1 (by simp [b.2]))⟩ : Fin (n + 1)) = 0 -- two cases for a = 0 or a > 0
    all_goals rename_i ha
    · apply le_sup_of_le_left
      apply le_sup_of_le_left
      simp only [h, ha, Fin.castSucc_zero, Fin.isValue, face_le']
    · dsimp
      rw [h]
      apply le_sup_of_le_right
      apply le_iSup_of_le <| ⟨a.1, by aesop⟩
      refine (le_of_eq_of_le') ?_ (face_le'' _ _ _ _ hj h ha)
      congr
      · ext
        refine Eq.symm (Fin.val_cast_of_lt (a.isLt.trans (Nat.lt_add_right 1 b.2)))
      · refine Eq.symm (Nat.mod_eq_of_lt (Nat.lt_add_right 1 b.2))
  · exact
    le_sup_of_le_left
      (le_sup_of_le_left
        (face_le ⟨a.succ, lt_of_le_of_lt a.succ.le_val_last (Nat.lt_add_right 1 (by simp [b.2]))⟩
          ⟨b.1, Nat.lt_add_right 1 b.isLt⟩ _ j hj h))

-- 0 < a ≤ b < n
-- Λ[n + 1, a + 1] ↪ Y(b, a - 1) = Y(b) ⊔ ... ⊔ σ (a - 1) b
open Subcomplex in
lemma hornProdSubcomplex_le₂' {n} (b : Fin n) (a : Fin b.succ.1) (h' : a.1 ≠ 0) :
    hornProdSubcomplex
      ⟨a, lt_of_le_of_lt a.is_le (Nat.lt_add_right 1 b.2)⟩ ⟨b.1, Nat.lt_add_right 1 b.2⟩ a.is_le ≤
        filtration₂ b ⟨a.pred (by aesop), (Nat.sub_one_lt h').trans a.isLt⟩ := by
  rw [hornProdSubcomplex_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases j = (⟨a, lt_of_le_of_lt a.is_le (Nat.lt_add_right 1 b.2)⟩ : Fin (n + 1)).castSucc -- check the a-th face first
  all_goals rename_i h
  · by_cases (⟨a, lt_of_le_of_lt a.is_le (Nat.lt_add_right 1 b.2)⟩ : Fin (n + 1)) = 0 -- two cases for a = 0 or a > 0
    all_goals rename_i ha
    · apply le_sup_of_le_left
      apply le_sup_of_le_left
      simp only [h, ha, Fin.castSucc_zero, Fin.isValue, face_le']
    · dsimp
      rw [h]
      apply le_sup_of_le_right
      apply le_iSup_of_le <| ⟨a.1.pred, by simp⟩
      refine (le_of_eq_of_le') ?_ (face_le'' _ _ _ _ hj h ha)
      congr
      · ext
        refine Eq.symm (Fin.val_cast_of_lt <| Nat.sub_one_lt_of_le (Nat.zero_lt_of_ne_zero h') (lt_of_le_of_lt a.is_le (Nat.lt_add_right 1 b.2)).le)
      · refine Eq.symm (Nat.mod_eq_of_lt (Nat.lt_add_right 1 b.2))
  · exact
    le_sup_of_le_left
      (le_sup_of_le_left
        (face_le ⟨a, lt_of_le_of_lt a.is_le (Nat.lt_add_right 1 b.2)⟩
          ⟨b.1, Nat.lt_add_right 1 b.isLt⟩ _ j hj h))

-- if X ≅ Y, then we have an order isomorphism of the subcomplexes
open Subcomplex in
def Subcomplex.orderIso {X Y : SSet} (f : X ≅ Y) : X.Subcomplex ≃o Y.Subcomplex where
  toFun A := A.image f.hom
  invFun B := B.image f.inv
  left_inv A := by aesop
  right_inv B := by aesop
  map_rel_iff' := by
    intro A A'
    simp
    constructor
    · intro h
      apply_fun (fun A ↦ (Subcomplex.image A f.inv)) at h
      simp at h
      convert h
      · aesop
      · aesop
      · refine Monotone.apply₂ ?_ f.inv
        refine Monotone.of_map_sup ?_
        aesop
    · intro h
      apply_fun (fun A ↦ (Subcomplex.image A f.hom)) at h
      exact h
      refine Monotone.apply₂ ?_ f.hom
      refine Monotone.of_map_sup ?_
      aesop

noncomputable
def Subcomplex.orderIso' {X Y : SSet} (f : X ⟶ Y) [hf : Mono f] :
    X.Subcomplex ≃o (Subcomplex.range f).toSSet.Subcomplex :=
  Subcomplex.orderIso (asIso <| toRangeSubcomplex f)

/- if f : X ⟶ Y, then we have an order hom from subcomplexes of the range into
 subcomplexes of Y -/
open Subcomplex in
def Subcomplex.orderHom {X Y : SSet} (f : X ⟶ Y) :
    (Subcomplex.range f).toSSet.Subcomplex →o (Y.Subcomplex) where
  toFun A := A.image (Subcomplex.range f).ι
  monotone' := by
    intro A A' h
    dsimp
    apply_fun (fun A ↦ Subcomplex.image A (range f).ι) at h
    exact h
    refine Monotone.apply₂ ?_ (range f).ι
    refine Monotone.of_map_sup ?_
    aesop

open Subcomplex in
lemma aux {X : SSet} (R : X.Subcomplex) (A : R.toSSet.Subcomplex) :
    A.image R.ι ⊓ range R.ι = A.image R.ι := by
  apply le_antisymm
  simp [Subpresheaf.range_ι, inf_le_left]
  apply le_inf (le_rfl) (image_le_range A _)

/- if f : X ⟶ Y is a mono, then we have an order hom from subcomplexes of the range
into subcomplexes of Y -/
open Subcomplex in
def Subcomplex.orderEmbedding {X Y : SSet} (f : X ⟶ Y) [Mono f] :
    (Subcomplex.range f).toSSet.Subcomplex ↪o (Y.Subcomplex) where
  toFun A := A.image (Subcomplex.range f).ι
  inj' := by
    intro A A' h
    dsimp at h
    apply_fun (fun A ↦ Subcomplex.preimage A (range f).ι) at h
    rwa [(preimage_eq_iff _ _ _).2 (aux (range f) A), (preimage_eq_iff _ _ _).2 (aux (range f) A')] at h
  map_rel_iff' := by
    have : Monotone (fun A ↦ Subcomplex.image A (range f).ι) := by
      refine Monotone.apply₂ ?_ (range f).ι
      refine Monotone.of_map_sup ?_
      aesop
    intro A A'
    dsimp
    constructor
    · intro h
      apply_fun (fun A ↦ Subcomplex.preimage A (range f).ι) at h
      dsimp at h
      rwa [(preimage_eq_iff _ _ _).2 (aux (range f) A), (preimage_eq_iff _ _ _).2 (aux (range f) A')] at h
      exact Monotone.of_map_inf fun x ↦ congrFun rfl
    · apply this

/- if R ≤ X, then we have an order isomorphism between subcomplexes of R and subcomplexes of X
contained in R -/
open Subcomplex in
def Subcomplex.orderIso'' {X : SSet} (R : X.Subcomplex) :
    OrderIso (R.toSSet.Subcomplex) {p : X.Subcomplex // p ≤ R} where
  toFun A := ⟨A.image R.ι, (image_le_iff A R.ι R).mpr (by simp only [Subcomplex.preimage_ι, le_top])⟩
  invFun := fun ⟨A, hA⟩ ↦ range (homOfLE hA)
  left_inv A := by aesop
  right_inv := fun ⟨B, hB⟩ ↦ by
    simp [Subcomplex.homOfLE, Subpresheaf.homOfLe]
    ext
    aesop
  map_rel_iff':= by
    intro A A'
    simp
    constructor
    · intro h
      apply_fun (fun A ↦ Subcomplex.preimage A R.ι) at h
      dsimp at h
      rwa [(preimage_eq_iff _ _ _).2 (aux R A), (preimage_eq_iff _ _ _).2 (aux R A')] at h
      have := preimage_eq_iff R.ι A (A.image R.ι)
      exact Monotone.of_map_inf fun x ↦ congrFun rfl
    · intro h
      apply_fun (fun A ↦ (Subcomplex.image A R.ι)) at h
      exact h
      refine Monotone.apply₂ ?_ R.ι
      refine Monotone.of_map_sup ?_
      aesop

-- bad proof because im lazy
open Subcomplex in
lemma image_le_boundary_iff' {n} {X : SSet} (f : Δ[n] ⟶ X) [Mono f]
      (A : (range f).toSSet.Subcomplex) :
    A ≤ ((boundary n).image (toRangeSubcomplex f)) ↔ A ≠ ⊤ := by
  constructor
  · intro h h'
    apply_fun (fun A ↦ Subcomplex.preimage A (asIso (toRangeSubcomplex f)).hom) at h
    dsimp at h
    have : (∂Δ[n].image (toRangeSubcomplex f)).preimage (toRangeSubcomplex f) = ∂Δ[n] := by
      apply le_antisymm
      · intro k x
        simp [toRangeSubcomplex, Subpresheaf.toRange, Subpresheaf.lift]
        intro y hy heq
        have := (NatTrans.mono_iff_mono_app f).1 (by infer_instance) k
        rw [mono_iff_injective] at this
        have := this heq
        (expose_names; exact Set.mem_of_eq_of_mem (this_1 (id (Eq.symm heq))) hy)
      · rw [← image_le_iff]
    rw [this, subcomplex_le_boundary_iff, h'] at h
    exact h rfl
    refine Monotone.apply₂ ?_ _
    refine Monotone.of_map_sup ?_
    exact fun x y ↦ rfl
  · intro h
    have : A.preimage (toRangeSubcomplex f) ≠ ⊤ := by
      intro h'
      apply h
      rw [preimage_eq_top_iff] at h'
      simp_all only [ne_eq, Subpresheaf.range_toRange, top_le_iff]
    rw [← subcomplex_le_boundary_iff] at this
    apply_fun (fun A ↦ Subcomplex.image A (toRangeSubcomplex f)) at this
    dsimp at this
    rw [preimage_image_of_isIso] at this
    exact this
    refine Monotone.apply₂ ?_ (toRangeSubcomplex f)
    refine Monotone.of_le_map_sup ?_
    intro j k l p i o
    aesop

-- bad proof because im lazy
open Subcomplex in
lemma image_le_boundary_iff {n} {X : SSet} (f : Δ[n] ⟶ X) [Mono f]
      (A : X.Subcomplex) (hA : A ≤ Subcomplex.range f) :
    A ≤ (boundary n).image f ↔ A ≠ (Subcomplex.range f) := by
  let bdry := image_le_boundary_iff' f ((orderIso'' (range f)).invFun ⟨A, hA⟩)
  constructor
  · intro h p
    refine bdry.1 ?_ ?_
    · rw [← (orderIso'' (range f)).map_rel_iff']
      simp [orderIso'']
      intro k x hx
      aesop
    · subst p
      simp [orderIso'']
      exact range_eq_top (𝟙 (range f).toSSet)
  · intro h
    have : (orderIso'' (range f)).invFun ⟨A, hA⟩ ≠ ⊤ := by
      intro h'
      apply h
      apply_fun (fun A ↦ Subcomplex.image A (range f).ι) at h'
      rw [image_top] at h'
      simp [orderIso''] at h'
      rw [← h']
      ext
      simp [image, Subcomplex.homOfLE, Subpresheaf.homOfLe]
      aesop
    rw [← bdry] at this
    apply_fun (fun A ↦ Subcomplex.image A (range f).ι) at this
    simp [orderIso''] at this
    have a : A = (range (Subcomplex.homOfLE hA)).image (range f).ι := by
      ext
      simp [Subcomplex.homOfLE, Subpresheaf.homOfLe]
      aesop
    have b : ∂Δ[n].image f = (∂Δ[n].image (toRangeSubcomplex f)).image (range f).ι := by aesop
    rwa [a, b]
    refine Monotone.apply₂ ?_ (range f).ι
    refine Monotone.of_le_map_sup ?_
    intro j k l p i o
    aesop

lemma hornProdSubcomplex_le_boundary_iff {a b hab} (A : (Δ[n] ⊗ Δ[2]).Subcomplex) (hA : A ≤ σ a b hab) :
    A ≤ (boundaryProdSubcomplex a b hab) ↔ A ≠ (σ a b hab) := by
  dsimp only [boundaryProdSubcomplex]
  rw [σeq] at hA ⊢
  apply image_le_boundary_iff (f a b hab) _ hA

open Subcomplex in
def mySq {n} (b : Fin n) (a : Fin b.1) :
    Subcomplex.Sq
      (hornProdSubcomplex
        ⟨a.1 + 1, lt_of_le_of_lt a.succ.le_val_last (Nat.lt_add_right 1 (by simp [b.2]))⟩
          b.castSucc (by simpa only [Fin.natCast_eq_last] using a.succ.le_val_last))
      (σ a.succ b (Fin.natCast_mono b.2.le (Fin.is_le a.succ)))
      (filtration₂ b a.castSucc)
      (filtration₂ b a.succ)
      where
  max_eq := by
    rw [filtration₂_succ n b a]
    aesop
  min_eq := by
    apply eq_of_le_of_le
    · dsimp [filtration₂]
      sorry
    · apply le_inf
      · refine le_of_eq_of_le' ?_ (hornProdSubcomplex_le₁ _ _ _)
        congr
        · exact Eq.symm (Nat.mod_eq_of_lt (lt_of_le_of_lt a.succ.le_val_last (by simp [Nat.lt_add_right 1 b.2])))
        · simp only [Fin.coe_eq_castSucc]
      · exact hornProdSubcomplex_le₂ _ _

-- show σ(a + 1)b ⊓ Y(b, a) = Λ[n + 1, (a + 1) + 1]
-- show σab ⊓ Y(b, a - 1) = Λ[n + 1, a + 1]

#check subcomplex_le_boundary_iff

#check Subcomplex.unionProd.isPushout (boundary n) (horn 2 1)

#check Subcomplex.Sq.commSq

#check Subcomplex.toOfSimplex

#check prodStdSimplex.objEquiv_nonDegenerate_iff

#check Subcomplex.le_iff_contains_nonDegenerate

#check Subcomplex.ofSimplex_le_iff

#check prodStdSimplex.mem_ofSimplex_iff

#check mem_ofSimplex_obj_iff
