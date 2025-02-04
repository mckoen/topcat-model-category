
import TopCatModelCategory.SSet.Horn
import TopCatModelCategory.SSet.DimensionProd
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

-- `0 ≤ a ≤ b ≤ n`
variable (n : ℕ)

/-- `[n + 1 + 1] → [n]`, defined for each `0 ≤ a ≤ b < n`. -/
-- might need to up the index by `1` since `n` could be `0`
def f₁ (a b : Fin (n + 1)) (hab : a ≤ b) : Fin (n + 2) →o Fin (n + 1) where
  toFun k :=
    if k ≤ a.castSucc.castSucc then k
    else Fin.pred k (sorry)
  monotone' := sorry

/-- `[n + 2] → [n]`, defined for each `0 ≤ a ≤ b ≤ n`. -/
def g₁ (a b : Fin (n + 1)) (hab : a ≤ b) : Fin (n + 3) →o Fin (n + 1) where
  toFun k :=
    if k ≤ (a : Fin (n + 3)) then k
    else if k ≤ b.succ then k - 1
    else k - 2
  monotone' := sorry

/-- `[n + 1 + 1] → [2]`. -/
def f₂ (a b : Fin (n + 1)) : Fin (n + 2) →o Fin 3 where
  toFun k :=
    if (k : ℕ) ≤ a then 0
    else if (k : ℕ) ≤ b + 1 then 1
    else 2
  monotone' := sorry

/-- `[n + 2] → [2]`. -/
abbrev g₂ (a b : Fin (n + 1)) : Fin (n + 3) →o Fin 3 := f₂ (n + 1) a b

open standardSimplex SimplexCategory in
noncomputable
def f {n} (a b : Fin (n + 1)) (hab : a ≤ b) : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] :=
  ((Δ[n] ⊗ Δ[2]).yonedaEquiv _).symm ⟨objMk (f₁ n a b hab), objMk (f₂ n a b)⟩

open standardSimplex Subcomplex in
noncomputable
def σ {n} (a b : Fin (n + 1)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  ofSimplex <| ((Δ[n] ⊗ Δ[2]).yonedaEquiv _) (f a b hab)
  --(ofSimplex (objMk (n := [n]) (f₁ n a b hab))).prod (ofSimplex (objMk (f₂ n a b)))

#check Subcomplex.toOfSimplex

open standardSimplex in
noncomputable
def τ {n} (a b : Fin (n + 1)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  Subcomplex.ofSimplexProd (objMk (g₁ n a b hab)) (objMk (g₂ n a b))
  /-
  FunctorToTypes.prod.lift (standardSimplex.map <| mkHom (f₁ n a b hab))
    (standardSimplex.map <| mkHom (f₂ n a b))
  -/

open SimplexCategory in
instance (a b : Fin (n + 1)) (hab : a ≤ b) : Mono (f a b hab) := by
  have : ∀ k, Mono ((f a b hab).app k) := by
    sorry
  apply NatTrans.mono_of_mono_app

open SimplexCategory in
def g' (a b : Fin (n + 1)) (hab : a ≤ b) : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  FunctorToTypes.prod.lift (standardSimplex.map <| mkHom (g₁ n a b hab))
    (standardSimplex.map <| mkHom (g₂ n a b))

open SimplexCategory in
instance : Mono (g' n a b hab) := by
  have : ∀ k, Mono ((g' n a b hab).app k) := by
    sorry
  apply NatTrans.mono_of_mono_app

/-- `Y(b)` for `0 ≤ b ≤ n`. Goes up to `Y(n)`, the first object in the `τ` filatration. -/
-- `Y(b) = Y(0) ⊔ [ σ00] ⊔ [σ01 ⊔ σ11] ⊔ ... ⊔ [σ0(b-1) ⊔ σ1(b-1) ⊔ ... ⊔ σ(b-1)(b-1)]`
noncomputable
def filtration₁ {n} (b : Fin (n + 1)) :
    (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (Subcomplex.unionProd (subcomplexBoundary n) (subcomplexHorn 2 1)) ⊔
    (⨆ (i : Fin b.1) (k : Fin i.succ.1), -- 0 ≤ k ≤ i ≤ b - 1
      σ ⟨k, lt_of_le_of_lt (Nat.le_of_lt_succ k.2) (i.2.trans b.2)⟩ ⟨i, (i.2.trans b.2)⟩
        (Fin.mk_le_mk.2 (Fin.is_le k)))

lemma filtration₁_zero :
    filtration₁ (0 : Fin (n + 1)) =
      (Subcomplex.unionProd (subcomplexBoundary n) (subcomplexHorn 2 1)) := by
  simp [filtration₁]

/-- `Y(b) ↪ Y(b + 1)` for `b < n` is just the union of `Y(b.castSucc)` with `[σ0b ⊔ ... ⊔ σbb]` -/
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

/-- `Y(b,a) = Y(b) ⊔ ... ⊔ σ (a - 1) b` for `0 ≤ a ≤ b < n`, if k : Fin a.1 -/
-- `Y(b,a) = Y(b) ⊔ ... ⊔ σ a b` for `0 ≤ a ≤ b < n`. if k : Fin.a.succ.1
noncomputable
def filtration₂ {n} (b : Fin n) (a : Fin b.succ.1) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (filtration₁ b) ⊔ (⨆ (k : Fin a.succ.1), σ k a sorry)

  /-
  (by
    refine (Fin.natCast_le_natCast ?_ ?_).mpr k.2.le
    exact (Nat.le_of_lt_succ ((k.2.trans a.2))).trans b.2.le
    exact (Nat.le_of_lt_succ a.2).trans b.2.le)) -- 0 ≤ k < a ≤ b < n
  -/

-- `Y(b,0) = Y(b) ∪ (σ00)` for `0 ≤ b < n`
-- if we adjust defn above then Y(b,0) = Y(b). not sure which is better
lemma filtration₂_zero (b : Fin n) :
    filtration₂ b ⟨0, Nat.zero_lt_succ b⟩ = filtration₁ b ⊔ (σ 0 0 le_rfl) := by
  simp [filtration₂]
  rfl


-- `Y(b,b) = Y(b) ⊔ σ0b ... ⊔ σbb`
-- `Y(b,b) = Y(b + 1)` for `0 ≤ b < n`
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

-- for `b < n`, `Y(b) ↪ Y(b + 1)` factors as `Y(b,0) ↪ Y(b,1) ↪ ... ↪ Y(b,b) ↪ Y(b + 1)`
-- e.g. `Y(n - 1) ↪ Y(n)` factors as `Y(n - 1,0) ↪ Y(n - 1,1) ↪ ... ↪ Y(n - 1,n - 1) ↪ Y(n)`

/-- `Y(b,a) ↪ Y(b, a + 1)` for `a < b ≤ n` is just the union of `Y(b,a+1)` with σab. -/
lemma filtration₂_succ (b : Fin n) (a : Fin b.1) :
    filtration₂ b a.succ = (filtration₂ b a.castSucc) ⊔
      (σ (a + 1) b (by
        refine Fin.add_one_le_of_lt ?_
        refine (Fin.natCast_lt_natCast (a.2.trans b.2).le b.2.le).mpr a.2
        )) := by
  simp [filtration₂]
  apply le_antisymm
  · apply sup_le (le_sup_of_le_left le_sup_left)
    sorry
  · apply sup_le
    · apply sup_le le_sup_left
      apply le_sup_of_le_left
      apply le_sup_of_le_right
      apply iSup_le
      intro i
      apply le_iSup₂_of_le a i
      apply le_of_eq
      congr
      all_goals refine Fin.eq_mk_iff_val_eq.mpr ?_
      all_goals simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      · exact (i.2.trans (Nat.add_lt_add_right a.2 1)).trans (Nat.add_lt_add_right b.2 1)
      · exact a.2.trans (Nat.lt_add_right 1 b.2)
    · sorry

-- the image of Λ[n + 1, a + 1] under σab : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]
noncomputable
def hornProdSubcomplex {n} (a b : Fin (n + 1)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  Subcomplex.image (subcomplexHorn (n + 1) (a.succ)) (f a b hab)

lemma hornProdSubcomplex_le₁ {n} (a b : Fin (n + 1)) (hab : a ≤ b) :
    hornProdSubcomplex a b hab ≤
      Subcomplex.unionProd (subcomplexBoundary n) (subcomplexHorn 2 1) := by
  dsimp [hornProdSubcomplex]
  rw [subcomplexHorn_eq_iSup (a.succ), Subcomplex.image_le_iff]
  apply iSup_le
  intro i
  rw [← Subcomplex.image_le_iff]
  sorry

lemma hornProdSubcomplex_le₂ {n} (a b : Fin (n + 1)) (hab : a ≤ b) :
    hornProdSubcomplex a b hab ≤ σ a b hab := by
  dsimp [hornProdSubcomplex]
  rw [Subcomplex.image_le_iff]
  simp [σ, f]
  sorry

def mySq (a b : Fin (n + 1)) (hab : a ≤ b) :
    Subcomplex.Sq (hornProdSubcomplex a b hab) (σ a b hab) sorry sorry where
  max_eq := sorry
  min_eq := sorry

#check Subcomplex.unionProd.isPushout (subcomplexBoundary n) (subcomplexHorn 2 1)

#check Subcomplex.Sq.commSq



--def mySq : Subcomplex.Sq
