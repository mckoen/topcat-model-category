
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

/-- `[n + 1 + 1] → [2]`. `0 ≤ a ≤ b < n` -/
def f₂ {n} (a b : Fin (n + 1)) (hab : a ≤ b) : Fin (n + 2) →o Fin 3 where
  toFun k :=
    if k ≤ a.castSucc then 0
    else if k ≤ b.succ then 1
    else 2
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

open standardSimplex SimplexCategory in
noncomputable
def f {n} (a b : Fin (n + 1)) (hab : a ≤ b) : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] :=
  ((Δ[n] ⊗ Δ[2]).yonedaEquiv _).symm ⟨⟨σ a⟩, objMk (f₂ a b hab)⟩

open standardSimplex SimplexCategory in
noncomputable
def g {n} (a b : Fin (n + 2)) (hab : a ≤ b) : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  ((Δ[n] ⊗ Δ[2]).yonedaEquiv _).symm ⟨objMk (g₁ a b), objMk (g₂ a b hab)⟩

open standardSimplex Subcomplex in
noncomputable
def σ {n} (a b : Fin (n + 1)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  ofSimplex <| ((Δ[n] ⊗ Δ[2]).yonedaEquiv _) (f a b hab)

open standardSimplex Subcomplex in
noncomputable
def τ {n} (a b : Fin (n + 2)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  ofSimplex <| ((Δ[n] ⊗ Δ[2]).yonedaEquiv _) (g a b hab)

lemma τeq : τ a b hab = Subcomplex.range (g a b hab) := rfl

lemma σeq : σ a b hab = Subcomplex.range (f a b hab) := rfl

open SimplexCategory in
instance (a b : Fin (n + 1)) (hab : a ≤ b) : Mono (f a b hab) := sorry

open SimplexCategory in
instance : Mono (g a b hab) := sorry

/-- `Y(b)` for `0 ≤ b ≤ n`. Goes up to `Y(n)`, the first object in the `τ` filtration. -/
-- `Y(b) = Y(0) ⊔ [σ00] ⊔ [σ01 ⊔ σ11] ⊔ ... ⊔ [σ0(b-1) ⊔ σ1(b-1) ⊔ ... ⊔ σ(b-1)(b-1)]`
-- ``Y(n) = Y(0) ⊔ [σ00] ⊔ [σ01 ⊔ σ11] ⊔ ... ⊔ [σ0(n-1) ⊔ σ1(n-1) ⊔ ... ⊔ σ(n-1)(n-1)]`
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
  rw [prodStandardSimplex.subcomplex_eq_top_iff _ rfl]
  intro z hz
  dsimp [filtration₃, filtration₁]
  apply Set.mem_union_right

  -- show that all nondegenerate n+2 simplices are contained in X(n).obj (n + 2). (they are in all the τ's)
  -- need to understand the nondegen simplices better
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
  Subcomplex.image (subcomplexHorn (n + 1) (a.succ)) (f a b hab)

-- linarith, omega

--image of i-th face under some f : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]
noncomputable
def SSet.face' {n} (i : Fin (n + 2)) (f : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  Subcomplex.image (standardSimplex.face {i}ᶜ) f

lemma hornProdSubcomplex_eq_iSup (a b : Fin (n + 1)) (hab : a ≤ b) :
    hornProdSubcomplex a b hab =
      ⨆ (j : ({a.succ}ᶜ : Set (Fin (n + 2)))), face' j.1 (f a b hab) := by
  dsimp [hornProdSubcomplex, face']
  rw [subcomplexHorn_eq_iSup]
  aesop

--def face (S : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex where
--  obj U := setOf (fun f ↦ Finset.image ((objEquiv _ _) f).toOrderHom ⊤ ≤ S)
--  map {U V} i := by
--    simp
--    intro x hx y
--    apply hx

lemma hornProdSubcomplex_le₁ {n} (a b : Fin (n + 1)) (hab : a ≤ b) :
    hornProdSubcomplex a b hab ≤
      Subcomplex.unionProd (subcomplexBoundary n) (subcomplexHorn 2 1) := by
  rw [hornProdSubcomplex_eq_iSup]
  apply iSup_le
  intro j

  sorry

open Subcomplex in
lemma hornProdSubcomplex_le₂ {n} (a b : Fin (n + 1)) (hab : a ≤ b) :
    hornProdSubcomplex.{u} a b hab ≤ σ a b hab := by
  rw [hornProdSubcomplex_eq_iSup]
  dsimp [face', σ]
  apply iSup_le
  intro ⟨j, hj⟩
  rw [standardSimplex.face_singleton_compl, image_ofSimplex, ofSimplex_le_iff,
    prodStandardSimplex.mem_ofSimplex_iff]
  intro i
  simp [Set.mem_range]
  intro k h
  exact ⟨_, h⟩

def mySq (a b : Fin (n + 1)) (hab : a ≤ b) :
    Subcomplex.Sq (hornProdSubcomplex a b hab) (σ a b hab) sorry sorry where
  max_eq := sorry
  min_eq := sorry

#check Subcomplex.unionProd.isPushout (subcomplexBoundary n) (subcomplexHorn 2 1)

#check Subcomplex.Sq.commSq

#check Subcomplex.toOfSimplex

#check prodStandardSimplex.objEquiv_non_degenerate_iff

#check Subcomplex.le_iff_contains_nonDegenerate

#check Subcomplex.ofSimplex_le_iff

#check prodStandardSimplex.mem_ofSimplex_iff
#check standardSimplex.mem_ofSimplex_obj_iff
