
import TopCatModelCategory.SSet.Horn
import TopCatModelCategory.SSet.DimensionProd
import TopCatModelCategory.SSet.NonDegenerateProdSimplex
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.Data.Sigma.Order

universe u

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

variable (n : ℕ)

@[simp]
def f₂' {n} (a b : Fin (n + 1)) : Fin (n + 2) → Fin 3 :=
  fun k ↦
    if k ≤ a.castSucc then 0
    else if k ≤ b.succ then 1
    else 2

/-- `[n + 1] → [2]`. `0 ≤ a ≤ b < n` -/
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
abbrev g₂ {n} (a b : Fin (n + 2)) (hab : a ≤ b) : Fin (n + 3) →o Fin 3 := f₂ a b hab

open SimplexCategory in
noncomputable
def f {n} (a b : Fin (n + 1)) (hab : a ≤ b) : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] :=
  SSet.yonedaEquiv.symm (stdSimplex.objEquiv.symm (σ a), stdSimplex.objMk (f₂ a b hab))

open SimplexCategory in
noncomputable
def g {n} (a b : Fin (n + 2)) (hab : a ≤ b) : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  SSet.yonedaEquiv.symm (stdSimplex.objEquiv.symm (σ b.succ ≫ σ a), stdSimplex.objMk (g₂ a b hab))

open Subcomplex in
noncomputable
def σ {n} (a b : Fin (n + 1)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  range (f a b hab)

open Subcomplex in
noncomputable
def τ {n} (a b : Fin (n + 2)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  range (g a b hab)

/-
namespace enumerate_nondegen

open SimplexCategory prodStdSimplex

variable {n : ℕ} (b : Fin (n + 2))

@[simp]
def ndg' (a : Fin b.succ) : Fin (n + 3) → Fin 3 :=
  fun k ↦
    if k ≤ (a : Fin (n + 3)) then 0
    else if k ≤ b.succ then 1
    else 2

def objMk₂ (a : Fin b.succ) : Δ[2] _⦋n + 2⦌  :=
  stdSimplex.objMk {
    toFun k :=
      if k ≤ (a : Fin (n + 3)) then 0
      else if k ≤ b.succ then 1
      else 2
    monotone' := by
      dsimp
      intro ⟨i, hi⟩ ⟨j, hj⟩ (hij : i ≤ j)
      rcases b with ⟨b, hb⟩
      rcases a with ⟨a, ha⟩
      dsimp
      sorry }

lemma objMk₂_injective : Function.Injective (objMk₂ (b := b) (n := n)) := sorry

lemma objMk₂_surjective : Function.Injective (objMk₂ (b := b) (n := n)) := sorry

def τ' (a : Fin b.succ) : (Δ[n] ⊗ Δ[2] : SSet) _⦋n + 2⦌ :=
  (stdSimplex.objEquiv.symm (σ b.succ ≫ σ a), objMk₂ b a)

instance (b : Fin (n + 1)) : OrderTop (Fin b.succ) where
  top := ⟨b, Nat.lt_add_one b⟩
  le_top a := Nat.le_of_lt_succ a.isLt


lemma _root_.Sigma.Fin_top_eq :
    (⊤ : Σₗ (b : Fin (n + 1)), Fin b.succ) = ⟨Fin.last n, Fin.last n⟩ := rfl

noncomputable
def _root_.Sigma.Fin_succ {n : ℕ} (i : Σₗ (b : Fin (n + 1)), Fin b.succ) (h : i ≠ ⊤) :
    Σₗ (b : Fin (n + 1)), Fin b.succ := by
  rw [← lt_top_iff_ne_top, Sigma.Fin_top_eq, Sigma.Lex.lt_def] at h
  dsimp at h

  sorry
  --⟨sorry, sorry⟩

def τ'' (i : Σₗ (b : Fin (n + 2)), Fin b.succ) : (Δ[n] ⊗ Δ[2] : SSet) _⦋n + 2⦌ :=
  (stdSimplex.objEquiv.symm (σ i.1.succ ≫ σ i.2), objMk₂ i.1 i.2)

def nonDegenerateEquiv₂.toFun (i : Σₗ (b : Fin (n + 2)), Fin b.succ) :
    (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 2) := by
  rcases i with ⟨b, a⟩
  refine ⟨τ' b a, ?_⟩
  rw [objEquiv_nonDegenerate_iff, Fin.orderHom_injective_iff]
  intro j h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  clear h
  simp [τ', objEquiv, stdSimplex.objMk₁, SimplexCategory.σ, objMk₂] at h₁ h₂
  by_cases h₃ : j.succ ≤ (a : Fin (n + 3))
  · have h₃' : j.castSucc ≤  (a : Fin (n + 3)) := Fin.le_of_lt h₃
    simp only [h₃, h₃'] at h₂

    sorry
  · simp [h₃] at h₂
    rw [not_le] at h₃
    have h₃' := Fin.le_castSucc_iff.2 h₃
    obtain h₃' | _ := h₃'.lt_or_eq
    ·
      rw [← not_le] at h₃'
      simp [h₃'] at h₂
      sorry
    · aesop

noncomputable
def nonDegenerateEquiv₂ :
    (Σₗ (b : Fin (n + 2)), Fin b.succ) ≃ (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 2) := by
  refine Equiv.ofBijective (nonDegenerateEquiv₂.toFun) ?_
  constructor
  · intro i j h
    rcases i with ⟨b, a⟩
    rcases j with ⟨b', a'⟩
    have := (congr_arg (Prod.fst ∘ Subtype.val) h)
    dsimp at this
    have := objMk₂_injective.{u} (n := n)
    dsimp [Function.Injective] at this

    sorry
  ·
    sorry

noncomputable abbrev simplex (j : Σₗ (b : Fin (n + 2)), Fin b.succ) := nonDegenerateEquiv₂ j

noncomputable abbrev ιSimplex (j : Σ (b : Fin (n + 2)), Fin b.succ) :
    (Δ[n + 2] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[2] :=
  SSet.yonedaEquiv.symm (simplex j)

instance (j : Σ (b : Fin (n + 2)), Fin b.succ) : Mono (ιSimplex.{u} j) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1 (nonDegenerateEquiv₂.{u} j).2

open Subcomplex in
noncomputable
def filtration₂ (j : Σₗ (b : Fin (n + 2)), Fin b.succ) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (unionProd (boundary n) (horn 2 1)) ⊔
    (⨆ (i : Σₗ (b : Fin (n + 2)), Fin b.succ) (_ : i < j), ofSimplex (simplex i).1)

lemma filtration₂_zero : filtration₂ ⟨0, ⟨0, Nat.zero_lt_succ _⟩⟩ =
    (Subcomplex.unionProd (boundary n) (horn 2 1)) := by
  dsimp [filtration₂]
  refine sup_eq_left.2 (le_of_eq_of_le ?_ bot_le)
  rw [iSup₂_eq_bot]
  intro ⟨b, a⟩ i
  rw [Sigma.Lex.lt_def] at i
  exfalso
  cases i
  · rename_i h
    simp only [Fin.not_lt_zero] at h
  · rename_i h
    simp only [Fin.not_lt_zero] at h
    obtain ⟨_, h⟩ := h
    exact h
  /-
  cases i
  · rename_i b a h
    exfalso
    exact h.not_le (Fin.zero_le _)
  · rename_i i hi
    have := Fin.le_zero_iff.mp hi
    subst this
    sorry
  -/

lemma monotone_filtration₂ : Monotone (filtration₂ (n := n)) := by
  intro x y hxy
  dsimp [filtration₂]
  apply sup_le (le_sup_left) (le_sup_of_le_right ?_)
  apply iSup₂_le
  intro i hi
  exact le_iSup₂_of_le i (sorry) (le_refl _)

lemma filtration₂_last : (filtration₂ (n := n)) ⊤ = ⊤ := by
  rw [prodStdSimplex.subcomplex_eq_top_iff _ rfl]
  intro x hx
  obtain ⟨i, hi⟩ := nonDegenerateEquiv₂.surjective ⟨x, hx⟩
  obtain rfl : simplex i = x := by simp_all only [simplex, Fin.val_succ]
  rw [filtration₂, ← Subcomplex.ofSimplex_le_iff]
  refine le_sup_of_le_right (le_iSup₂_of_le i ?_ (le_refl _))
  sorry

end enumerate_nondegen
-/

open stdSimplex

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
  simp [SimplexCategory.σ, Hom.toOrderHom, CategoryStruct.comp,
    OrderHom.comp] at H
  apply_fun (fun f ↦ f.toOrderHom e) at H'
  simp [Hom.toOrderHom, objMk, g₂, objEquiv,
    Equiv.ulift, Hom.mk, CategoryStruct.comp, OrderHom.comp, f₂] at H H'
  fin_cases e
  simp at H
  dsimp at H'
  simp [Fin.predAbove] at H
  have A : (a : Fin (n + 1)).castSucc.succ < (((b.1 + 1) : ℕ) : Fin (n + 2)).castSucc := sorry
  split at H
  simp_rw [Fin.lt_pred_iff] at H
  · next h' =>
    simp_all
    simp [A.trans h'] at H
    have B : ¬ g' 0 ≤ a.castSucc := by
      rw [not_le]
      have : a.castSucc < (a : Fin (n + 1)).castSucc.succ := by
        sorry
      convert this.trans (A.trans h')
    have C : ¬ g' 0 ≤ b.succ := by
      sorry
    dsimp [ConcreteCategory.hom, Hom.toOrderHom] at B C
    simp [B, C] at H'
    split at H'
    · next => simp only [Fin.isValue, Fin.reduceEq] at H'
    · next h'' =>
      simp_all
      split at H'
      · next => simp only [Fin.isValue, Fin.reduceEq] at H'
      · next h''' =>
        simp_all
        split at H
        · next q => simpa only [Fin.lt_pred_iff, A.trans q, Fin.isValue, ↓reduceDIte, Fin.pred_inj] using H
        · next q =>
          exfalso
          rw [not_lt] at q
          have := lt_of_lt_of_le h''' q
          apply this.not_le (le_of_eq ?_)
          ext
          simp
          change b.1 + 1 ≤ n + 1
          apply Nat.le_of_lt_succ
          change b.1 + 1 < n + 2
          suffices b.succ < Fin.last (n + 2) by
            simp [Fin.last, Fin.succ] at this
            simpa
          exact (@Fin.lt_last_iff_ne_last (n + 2) b.succ).2 (Fin.ne_last_of_lt C)
  · next h' =>
    simp_rw [Fin.lt_castPred_iff] at H
    rw [not_lt] at h'
    split at H
    · next h'' =>
      simp_all
      sorry
    · next h'' =>
      rw [not_lt] at h''
      sorry

/-- `X(b)` for `0 ≤ b ≤ n`. Goes up to `X(n)`, the first object in the `τ` filtration.
`X(b) = X(0) ⊔ [σ00] ⊔ [σ01 ⊔ σ11] ⊔ ... ⊔ [σ0(b-1) ⊔ σ1(b-1) ⊔ ... ⊔ σ(b-1)(b-1)]` -/
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

/-- `X(b) ↪ X(b + 1)` for `b < n` is just the union of `X(b.castSucc)` with `[σ0b ⊔ ... ⊔ σbb]` -/
-- `X(n - 1) ↪ X(n)` is just the union of `X(n - 1)` with `[σ0(n - 1) ⊔ ... ⊔ σ(n - 1)(n - 1)]`
lemma filtration₁_succ (b : Fin n) :
    filtration₁ b.succ =
      filtration₁ b.castSucc ⊔ -- 0 ≤ i ≤ b, ⨆ σib
        (⨆ (i : Fin b.succ.1), σ ⟨i, by omega⟩ b.castSucc (Fin.le_castSucc_iff.mpr i.2)) := by
  simp [filtration₁]
  apply le_antisymm
  · apply sup_le
    · apply le_sup_of_le_left (le_sup_of_le_left le_rfl)
    · apply iSup₂_le
      intro i k
      by_cases i.1 < b; all_goals rename_i h
      · exact le_sup_of_le_left (le_sup_of_le_right (le_iSup₂_of_le ⟨i, h⟩ k le_rfl))
      · have : i.1 = b := by
          rw [not_lt] at h
          refine le_antisymm (Fin.is_le i) h
        apply le_sup_of_le_right
        apply le_iSup_of_le ⟨k, by simp [← this]⟩
        simp [this]
        rfl
  · apply sup_le
    · apply sup_le le_sup_left
      · exact le_sup_of_le_right
          (iSup₂_le fun i k ↦ le_iSup₂_of_le ⟨i, Nat.lt_add_right 1 i.isLt⟩ k le_rfl)
    · refine le_sup_of_le_right (iSup_le fun i ↦ le_iSup₂_of_le ⟨b, by simp⟩ i le_rfl)

-- `X(b,a) = X(b) ⊔ ... ⊔ σ a b` for `0 ≤ a ≤ b < n`. if k : Fin a.succ.1
-- `X(b,b) = X(b) ⊔ σ0b ... ⊔ σbb = X(b + 1)`
-- `X(n - 1, n - 1) = X(n - 1) ⊔ σ0(n - 1) ... ⊔ σ(n - 1)(n - 1) = X(n)`
noncomputable
def filtration₂ {n} (b : Fin n) (a : Fin b.succ.1) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (filtration₁ b.castSucc) ⊔ (⨆ (k : Fin a.succ.1), σ k b (by
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    rcases k with ⟨k, hk⟩
    dsimp at ha hk ⊢
    refine (Fin.natCast_le_natCast ?_ ?_).mpr ?_
    all_goals linarith))

-- `X(b,0) = X(b) ∪ (σ 0 b)` for `0 ≤ b < n`
lemma filtration₂_zero (b : Fin n) :
    filtration₂ b ⟨0, Nat.zero_lt_succ b⟩ = filtration₁ b ⊔ (σ 0 b (Fin.zero_le _)) := by
  simp [filtration₂]
  rfl

-- `X(b,b) = X(b + 1)` for `0 ≤ b < n`
-- `X(0, 0) = X(0) ⊔ σ00 = X(1)`
-- `X(n - 1, n - 1) = X(n)`
lemma filtration₂_last (b : Fin n) :
    filtration₂ b ⟨b, Nat.lt_add_one b⟩ = filtration₁ b.succ := by
  simp [filtration₂]
  rw [filtration₁_succ]
  apply le_antisymm
  · refine sup_le (le_sup_of_le_left le_rfl) (le_sup_of_le_right (iSup_le fun i ↦ ?_))
    have : (i : Fin (n + 1)) = ⟨i, LT.lt.trans i.isLt b.succ.isLt⟩ := by
      refine Fin.eq_mk_iff_val_eq.mpr ?_
      simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      refine i.2.trans (Nat.add_lt_add_right b.2 1)
    simp_rw [this]
    exact le_iSup_iff.mpr fun b_1 a ↦ a i
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
-- `X(b,a) = X(b) ⊔ ... ⊔ σab`
-- `X(b,a + 1) = X(b) ⊔ ... ⊔ σ(a + 1)b`
/-- `X(b,a) ↪ X(b, a + 1)` for `a < b ≤ n` is just the union of `X(b,a)` with `σ(a + 1)b`. -/
lemma filtration₂_succ (b : Fin n) (a : Fin b.1) :
    filtration₂ b a.succ = (filtration₂ b a.castSucc) ⊔
      (σ a.succ b (Fin.natCast_mono b.2.le (Fin.is_le a.succ))) := by
  dsimp [filtration₂]
  apply le_antisymm
  · refine sup_le (le_sup_of_le_left le_sup_left) (iSup_le fun ⟨i, hi⟩ ↦ ?_)
    cases lt_or_eq_of_le (Nat.le_of_lt_succ hi); all_goals rename_i h
    · exact le_sup_of_le_left (le_sup_of_le_right (le_iSup_of_le ⟨i, h⟩ (le_rfl)))
    · subst h
      exact le_sup_of_le_right le_rfl
  · apply sup_le
    · exact sup_le le_sup_left
        (le_sup_of_le_right (iSup_le (fun i ↦ le_iSup_of_le ⟨i, by omega⟩ le_rfl)))
    · exact le_sup_of_le_right (le_iSup_of_le ⟨a + 1, lt_add_one _⟩ le_rfl)

/-- `Y(b)` for `0 ≤ b ≤ n + 1`. Goes up to `Y(n + 1)`. -/
-- `Y(b) = X(n) ⊔ [τ00] ⊔ [τ01 ⊔ τ11] ⊔ ... ⊔ [τ0(b-1) ⊔ τ1(b-1) ⊔ ... ⊔ τ(b-1)(b-1)]`
-- `Y(n + 1) = Y(n) ⊔ [τ0n ⊔ τ1n ⊔ ... ⊔ τnn]`
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

/-- `Y(b) ↪ Y(b + 1)` for `b < n + 1` is just the union of `Y(b.castSucc)` with `[τ0b ⊔ ... ⊔ τbb]` -/
-- `Y(n) ↪ Y(n + 1)` is just the union of `Y(n)` with `[τ0n ⊔ ... ⊔ τnn]`
lemma filtration₃_succ (b : Fin (n + 1)) :
    filtration₃ b.succ =
      filtration₃ b.castSucc ⊔ -- 0 ≤ i ≤ b, ⨆ σib
        (⨆ (i : Fin b.succ.1), τ ⟨i, i.2.trans b.succ.2⟩ b.castSucc (Fin.le_castSucc_iff.mpr i.2)) := by
    dsimp [filtration₁]
    apply le_antisymm
    · apply sup_le (le_sup_of_le_left (le_sup_of_le_left le_rfl))
      · apply iSup₂_le (fun i k ↦ ?_)
        by_cases i.1 < b; all_goals rename_i h
        · exact le_sup_of_le_left (le_sup_of_le_right (le_iSup₂_of_le ⟨i, h⟩ k le_rfl))
        · have : i.1 = b := by
            rw [not_lt] at h
            refine le_antisymm (Fin.is_le i) h
          refine le_sup_of_le_right (le_iSup_of_le ⟨k, by simp [← this]⟩ ?_)
          simp [this]
          rfl
    · apply sup_le
      · apply sup_le (le_sup_of_le_left le_rfl)
        · exact le_sup_of_le_right
            (iSup₂_le fun i k ↦ le_iSup₂_of_le ⟨i, Nat.lt_add_right 1 i.isLt⟩ k le_rfl)
      · exact le_sup_of_le_right (iSup_le fun i ↦ le_iSup₂_of_le ⟨b, Nat.lt_add_one b⟩ i le_rfl)

-- should redefine the filtration in terms of the equivalence between the τ's and the nondegen
-- simplices, as joel does.
lemma filtration₃_last : filtration₃ (n.succ) = (⊤ : (Δ[n] ⊗ Δ[2]).Subcomplex) := by
  rw [prodStdSimplex.subcomplex_eq_top_iff _ rfl]
  intro z hz
  --#check prodStandardSimplex.objEquiv_non_degenerate_iff
  --#check standardSimplex.mem_non_degenerate_iff_mono
  -- show that all nondegenerate n+2 simplices are contained in X(n).obj (n + 2). (they are all the τ's)
  sorry

-- `Y(b,a) = Y(b) ⊔ ... ⊔ τ a b` for `0 ≤ a ≤ b ≤ n`.
-- `Y(b,a + 1) = Y(b) ⊔ ... ⊔ τ (a + 1) b`
-- `Y(b,b) = Y(b) ⊔ τ0b ... ⊔ τbb = Y(b + 1)`
-- `Y(n, n) = Y(n) ⊔ τ0n ... ⊔ τnn = Y(n + 1) = Δ[n] ⊗ Δ[2]`
noncomputable
def filtration₄ {n} (b : Fin (n + 1)) (a : Fin b.succ.1) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (filtration₃ b) ⊔ (⨆ (k : Fin a.succ.1), τ k b (by
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    rcases k with ⟨k, hk⟩
    dsimp at ha hk ⊢
    refine (Fin.natCast_le_natCast ?_ ?_).mpr ?_
    all_goals linarith))

-- `Y(b,0) = Y(b) ∪ (τ0b)` for `0 ≤ b ≤ n`
lemma filtration₄_zero (b : Fin (n + 1)) :
    filtration₄ b ⟨0, Nat.zero_lt_succ b⟩ = filtration₃ b ⊔ (τ 0 b (Fin.zero_le _)) := by
  simp [filtration₄]
  rfl

-- `Y(b,b) = X(b + 1)` for `0 ≤ b < n + 1`
-- `Y(0, 0) = X(n) ⊔ τ00 = Y(1)`
-- `Y(n, n) = Y(n + 1)`
lemma filtration₄_last (b : Fin (n + 1)) :
    filtration₄ b ⟨b, Nat.lt_add_one b⟩ = filtration₃ b.succ := by
  simp [filtration₄]
  rw [filtration₃_succ]
  apply le_antisymm
  · refine sup_le (le_sup_of_le_left le_rfl) (le_sup_of_le_right (iSup_le fun i ↦ ?_))
    have : (i : Fin (n + 2)) = ⟨i, LT.lt.trans i.isLt b.succ.isLt⟩ := by
      refine Fin.eq_mk_iff_val_eq.mpr ?_
      simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      refine i.2.trans (Nat.add_lt_add_right b.2 1)
    simp_rw [this]
    exact le_iSup_iff.mpr fun b_1 a ↦ a i
  · refine sup_le (le_sup_of_le_left le_rfl) (le_sup_of_le_right (iSup_le fun i ↦ ?_))
    apply le_iSup_of_le i
    have : (i : Fin (n + 2)) = ⟨i, i.isLt.trans b.succ.isLt⟩ := by
      refine Fin.eq_mk_iff_val_eq.mpr ?_
      simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      refine i.2.trans (Nat.add_lt_add_right b.2 1)
    simp_rw [this]
    rfl

/-- `Y(b,a) ↪ Y(b, a + 1)` for `a < b ≤ n + 1` is just the union of `Y(b,a)` with `τ(a + 1)b`. -/
lemma filtration₄_succ (b : Fin (n + 2)) (a : Fin b.1) :
    filtration₄ b a.succ = (filtration₄ b a.castSucc) ⊔
      (τ a.succ b (Fin.natCast_mono b.2.le (Fin.is_le a.succ))) := by
  simp [filtration₄]
  apply le_antisymm
  · refine sup_le (le_sup_of_le_left le_sup_left) (iSup_le fun ⟨i, hi⟩ ↦ ?_)
    cases lt_or_eq_of_le (Nat.le_of_lt_succ hi); all_goals rename_i h
    · exact le_sup_of_le_left (le_sup_of_le_right (le_iSup_of_le ⟨i, h⟩ le_rfl))
    · apply le_sup_of_le_right
      simp_rw [h]
      rfl
  · apply sup_le
    · exact sup_le le_sup_left
        (le_sup_of_le_right (iSup_le fun i ↦ le_iSup_of_le ⟨i, Nat.lt_add_right 1 i.2⟩ le_rfl))
    · exact le_sup_of_le_right (le_iSup_of_le ⟨a + 1, lt_add_one _⟩ le_rfl)

lemma filtration₄_last' : filtration₄ n ⟨n, by simp⟩ = (⊤ : (Δ[n] ⊗ Δ[2]).Subcomplex) := by
  have h₁ := filtration₄_last n n
  have h₂ := filtration₃_last n
  simp at h₁ h₂
  rw [h₁, h₂]

open Subcomplex

/-- the image of Λ[n + 1, a + 1] under σab : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] -/
@[simp]
noncomputable
def hornProdSubcomplex {n} (a b : Fin (n + 1)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (horn (n + 1) a.succ).image (f a b hab)

/-- the image of ∂Δ[n + 1] under σab : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] -/
@[simp]
noncomputable
def boundaryProdSubcomplex {n} (a b : Fin (n + 1)) (hab : a ≤ b) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (boundary (n + 1)).image (f a b hab)

/-- image of i-th face under some f : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] -/
@[simp]
noncomputable
def faceProdSubcomplex {n} (i : Fin (n + 2)) (f : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (face {i}ᶜ).image f

-- image of Λ[n + 1, a + 1] under (f a b hab) is the union of the image under f of all faces except
-- the (a + 1)-th
lemma hornProdSubcomplex_eq_iSup (a b : Fin (n + 1)) (hab : a ≤ b) :
    hornProdSubcomplex a b hab =
      ⨆ (j : ({a.succ}ᶜ : Set (Fin (n + 2)))), faceProdSubcomplex j.1 (f a b hab) := by
  simp only [hornProdSubcomplex, horn_eq_iSup, image_iSup, faceProdSubcomplex]

lemma boundaryProdSubcomplex_eq_iSup (a b : Fin (n + 1)) (hab : a ≤ b) :
    boundaryProdSubcomplex a b hab =
      ⨆ (j : Fin (n + 2)), faceProdSubcomplex j.1 (f a b hab) := by
  simp only [boundaryProdSubcomplex, boundary_eq_iSup, image_iSup, faceProdSubcomplex,
    Fin.cast_val_eq_self]

lemma hornProdSubcomplex_le_σ {n} (a b : Fin (n + 1)) (hab : a ≤ b) :
    hornProdSubcomplex.{u} a b hab ≤ σ a b hab := by
  rw [hornProdSubcomplex_eq_iSup]
  exact iSup_le fun j ↦ image_le_range _ (f a b hab)

lemma face_le_σ {n} (a b : Fin (n + 1)) (hab : a ≤ b) (j : Fin (n + 2)) :
    faceProdSubcomplex j (f a b hab) ≤ σ a b hab := image_le_range _ (f a b hab)

/-- each face of σab except the a-th and (a+1)-th is contained in (boundary n).unionProd (horn 2 1) -/
lemma face_le_boundary_unionProd_horn {n} (a b : Fin (n + 1)) (hab : a ≤ b)
    (j : Fin (n + 2)) (hj : ¬j = a.succ) (hj' : ¬j = a.castSucc) :
      faceProdSubcomplex j (f a b hab) ≤ (boundary n).unionProd (horn 2 1) := by
  dsimp [unionProd, faceProdSubcomplex]
  apply le_sup_of_le_right
  rw [face_singleton_compl, image_ofSimplex, ofSimplex_le_iff]
  refine ⟨?_, by simp only [Subpresheaf.top_obj, Set.top_eq_univ, Set.mem_univ]⟩
  change ¬Function.Surjective (a.predAbove ∘ j.succAbove) --this is the crux of the proof
  intro h'
  have : j < a.castSucc ∨ a.succ < j := by
    cases Fin.lt_or_lt_of_ne hj
    all_goals cases Fin.lt_or_lt_of_ne hj'
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

/-- the 0-th face of σ0b is contained in the unionProd -/
lemma zero_face_le {n} (b : Fin (n + 1)):
      faceProdSubcomplex 0 (f 0 b b.zero_le) ≤ (boundary n).unionProd (horn 2 1) := by
  dsimp [Subcomplex.unionProd, faceProdSubcomplex]
  apply le_sup_of_le_left
  rw [face_singleton_compl, image_ofSimplex, ofSimplex_le_iff]
  simp
  refine ⟨trivial, ?_⟩
  change Set.range (f₂' 0 b ∘ Fin.succ) ∪ {1} ≠ Set.univ
  intro h'
  rw [Set.eq_univ_iff_forall] at h'
  have h'' := h' 0
  simp at h''
  obtain ⟨e, he⟩ := h''
  have := he e.succ_ne_zero
  aesop

/-- for a > 0 the a-th face of σab is the a-th face of σ(a-1)b -/
lemma face_eq_face_pred {n} (a b : Fin (n + 1)) (hab : a ≤ b) (ha : ¬a = 0) :
    faceProdSubcomplex a.castSucc (f a b hab) =
      faceProdSubcomplex a.castSucc (f (a.castSucc.pred (Fin.castSucc_ne_zero_iff.mpr ha)) b
        (by rw [Fin.pred_le_iff]; exact ((Fin.castSucc_le_castSucc_iff.2 hab).trans (Fin.castSucc_le_succ b)))) := by
  dsimp [Subcomplex.unionProd, faceProdSubcomplex]
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

/-- the a-th face of σab is contained in σ(a-1)b -/
lemma face_le_σ_pred {n} (a b : Fin (n + 1)) (hab : a ≤ b) (ha : a ≠ 0) :
    faceProdSubcomplex a.castSucc (f a b hab) ≤ σ (a.castSucc.pred (Fin.castSucc_ne_zero_iff.mpr ha)) b
      ((Fin.pred_castSucc_lt (Fin.castSucc_ne_zero_iff.mpr ha)).le.trans hab) := by
  rw [face_eq_face_pred a b hab ha]
  exact image_le_range _ _

/-- the a-th face of σab is contained in σ(a-1)b -/
lemma face_succ_le_σ {n} (a b : Fin (n + 1)) (hab : a ≤ b) :
    faceProdSubcomplex a.succ (f a b hab) ≤ σ a b hab := by
  exact image_le_range _ _

/-- for 0 ≤ a < b < n, Λ[n + 1, (a + 1) + 1] ≤ X(b,a) = X(b) ⊔ ... ⊔ σ a b -/
lemma hornProdSubcomplex_le_filt {n} (b : Fin n) (a : Fin b.1) :
    hornProdSubcomplex a.succ.1 b.castSucc ((Fin.natCast_mono b.is_lt.le a.succ.is_le).trans (by simp))
      ≤ filtration₂ b a.castSucc := by
  rw [hornProdSubcomplex_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = (a.succ : Fin (n + 1)).castSucc -- check the a-th face first
  · by_cases ha : (a.succ : Fin (n + 1)) = 0 -- two cases for a = 0 or a > 0
    · refine le_sup_of_le_left (le_sup_of_le_left ?_)
      simp only [h, ha, Fin.castSucc_zero, Fin.isValue, zero_face_le]
    · subst h
      refine le_sup_of_le_right
        (le_iSup_of_le ⟨a.1 , Nat.lt_add_one a⟩ (le_of_eq_of_le' ?_ (face_le_σ_pred _ _ _ ha)))
      congr
      · have : (a.succ : Fin (n + 1)) = (⟨a, a.2.trans b.2⟩ : Fin n).succ := by
          ext
          simp [a.2.trans b.2]
        simp_rw [this, Fin.pred_castSucc_succ]
        exact Fin.eq_of_val_eq (Fin.val_cast_of_lt (Nat.lt_add_right 1 (a.isLt.trans b.isLt))).symm
      · exact Fin.coe_eq_castSucc.symm
  · exact le_sup_of_le_left (le_sup_of_le_left (face_le_boundary_unionProd_horn _ _ _ j hj h))

/-
/-- for 0 < a ≤ b < n, Λ[n + 1, a + 1] ≤ X(b, a - 1) = X(b) ⊔ ... ⊔ σ (a - 1) b -/
lemma hornProdSubcomplex_le_filt' {n} (b : Fin n) (a : Fin b.succ.1) (h' : a.1 ≠ 0) :
    hornProdSubcomplex
      ⟨a, lt_of_le_of_lt a.is_le (Nat.lt_add_right 1 b.2)⟩ b (Fin.mk_le_of_le_val (by simp [Fin.is_le])) ≤
        filtration₂ b ⟨a.pred (by aesop), (Nat.sub_one_lt h').trans a.isLt⟩ := by
  rw [hornProdSubcomplex_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = (⟨a, lt_of_le_of_lt a.is_le (Nat.lt_add_right 1 b.2)⟩ : Fin (n + 1)).castSucc -- check the a-th face first
  · subst h
    refine le_sup_of_le_right
      (le_iSup_of_le ⟨a.1.pred, by simp⟩ (le_of_eq_of_le' ?_ (face_le_σ_pred _ _ _ (by simp [h']))))
    congr
    · ext
      refine Eq.symm (Fin.val_cast_of_lt <| Nat.sub_one_lt_of_le (Nat.zero_lt_of_ne_zero h') (lt_of_le_of_lt a.is_le (Nat.lt_add_right 1 b.2)).le)
  · exact le_sup_of_le_left (le_sup_of_le_left (face_le_boundary_unionProd_horn _ b _ j hj h))
-/

def image_monotone {X Y : SSet} (f : X ⟶ Y) :
    Monotone (fun (A : Subcomplex X) ↦ A.image f) := by
  refine Monotone.apply₂ (Monotone.of_map_sup ?_) f
  intro A B
  ext
  aesop

def preimage_monotone {X Y : SSet} (f : X ⟶ Y) :
    Monotone (fun (B : Subcomplex Y) ↦ B.preimage f) := by
  refine Monotone.apply₂ (Monotone.of_map_sup ?_) f
  intro A B
  ext
  aesop

/-- if X ≅ Y, then we have an order isomorphism of their subcomplexes -/
@[simps!]
def subcomplex_orderIso {X Y : SSet} (f : X ⟶ Y) [IsIso f] : X.Subcomplex ≃o Y.Subcomplex where
  toFun A := A.image f
  invFun B := B.preimage f
  left_inv A := image_preimage_of_isIso f A
  right_inv B := preimage_image_of_isIso f B
  map_rel_iff' := ⟨fun h ↦ by simpa using preimage_monotone f h, fun h ↦ image_monotone f h⟩

@[simps!]
def range_orderIso {X Y : SSet} (f : X ⟶ Y) [hf : Mono f] :
    X.Subcomplex ≃o (range f).toSSet.Subcomplex :=
  subcomplex_orderIso (toRangeSubcomplex f)

@[simp]
lemma subcomplex_orderIso.symm_apply_eq' {X Y : SSet} (f : X ⟶ Y) [hf : IsIso f] (A : Subcomplex X) :
    (subcomplex_orderIso f).symm (A.image f) = A := (OrderIso.symm_apply_eq _).2 rfl

/-- if f : X ⟶ Y, then we have an order hom from subcomplexes of the range into
 subcomplexes of Y -/
 @[simps!]
def subcomplex_orderHom {X Y : SSet} (f : X ⟶ Y) :
    (Subcomplex.range f).toSSet.Subcomplex →o (Y.Subcomplex) where
  toFun A := A.image (range f).ι
  monotone' := image_monotone _

@[simp]
lemma aux {X : SSet} (R : X.Subcomplex) (A : R.toSSet.Subcomplex) :
    A.image R.ι ⊓ range R.ι = A.image R.ι := by
  apply le_antisymm
  simp [Subpresheaf.range_ι, inf_le_left]
  apply le_inf (le_rfl) (image_le_range A _)

/-- if f : X ⟶ Y is a mono, then we have an order embedding from subcomplexes of the range
into subcomplexes of Y -/
@[simps!]
def subcomplex_orderEmbedding {X Y : SSet} (f : X ⟶ Y) [Mono f] :
    (range f).toSSet.Subcomplex ↪o (Y.Subcomplex) where
  toFun A := A.image (range f).ι
  inj' := by
    intro A A' h
    dsimp at h
    apply_fun (fun A ↦ Subcomplex.preimage A (range f).ι) at h
    rwa [(preimage_eq_iff _ _ _).2 (aux (range f) A),
      (preimage_eq_iff _ _ _).2 (aux (range f) A')] at h
  map_rel_iff' := by
    intro A A'
    dsimp
    constructor
    · intro h
      have := preimage_monotone (range f).ι h
      dsimp at this
      rwa [(preimage_eq_iff _ _ _).2 (aux (range f) A),
        (preimage_eq_iff _ _ _).2 (aux (range f) A')] at this
    · apply image_monotone

/-- if R ≤ X, then we have an order isomorphism between subcomplexes of R and subcomplexes of X
contained in R -/
@[simps!]
def subset_orderIso {X : SSet} (R : X.Subcomplex) :
    (R.toSSet.Subcomplex) ≃o {p : X.Subcomplex // p ≤ R} where
  toFun A := ⟨A.image R.ι, by simpa only [Subpresheaf.range_ι] using image_le_range A R.ι⟩
  invFun := fun ⟨A, hA⟩ ↦ range (homOfLE hA)
  left_inv A := by aesop
  right_inv := fun ⟨B, hB⟩ ↦ by
    simp [Subcomplex.homOfLE, Subpresheaf.homOfLe]
    ext
    aesop
  map_rel_iff' := by
    intro A A'
    simp
    constructor
    · intro h
      have := preimage_monotone R.ι h
      dsimp at this
      rwa [(preimage_eq_iff _ _ _).2 (aux R A), (preimage_eq_iff _ _ _).2 (aux R A')] at this
    · intro h
      exact image_monotone _ h

/-
lemma image_le_boundary_iff' {n} {X : SSet} (f : Δ[n] ⟶ X) [Mono f]
      (A : (range f).toSSet.Subcomplex) :
    A ≤ ((boundary n).image (toRangeSubcomplex f)) ↔ A ≠ ⊤ := by
  constructor
  · intro h h'
    rw [← (range_orderIso f).symm.map_rel_iff'] at h
    simp [range_orderIso, subcomplex_orderIso.symm_apply_eq'] at h
    rw [subcomplex_le_boundary_iff, h'] at h
    exact h rfl
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
-/

lemma helper {X Y : SSet} (f : X ⟶ Y) (A : Subcomplex X) :
    range (Subcomplex.homOfLE (image_le_range A f)) = A.image (toRangeSubcomplex f) := by
  aesop

lemma helper' {X Y : SSet} (f : X ⟶ Y) [Mono f] (A : Subcomplex X) :
    (range_orderIso f).symm ((subset_orderIso (range f)).symm ⟨A.image f, image_le_range A f⟩) = A := by
  dsimp [range_orderIso, subcomplex_orderIso, subset_orderIso, OrderIso.symm]
  rw [helper]
  exact image_preimage_of_isIso (toRangeSubcomplex f) A

-- bad proof
lemma image_le_boundary_iff {n} {X : SSet} (f : Δ[n] ⟶ X) [Mono f]
    (A : X.Subcomplex) (hA : A ≤ range f) :
      A ≤ (boundary n).image f ↔ A ≠ (range f) := by
  let iso := OrderIso.trans (subset_orderIso (range f)).symm (range_orderIso f).symm
  have : iso ⟨∂Δ[n].image f, image_le_range _ _⟩ = ∂Δ[n] := helper' _ _
  constructor
  · intro h
    replace h : (⟨A, hA⟩ : {p : X.Subcomplex // p ≤ range f}) ≤
      ⟨∂Δ[n].image f, image_le_range _ _⟩ := h
    rw [← iso.map_rel_iff', RelIso.coe_fn_toEquiv, this, subcomplex_le_boundary_iff] at h
    intro h'
    subst h'
    apply h
    simp [iso, subset_orderIso, OrderIso.symm, range_eq_top_iff]
    infer_instance
  · intro h
    change (⟨A, hA⟩ : {p : X.Subcomplex // p ≤ range f}) ≤
      ⟨∂Δ[n].image f, image_le_range _ _⟩
    rw [← iso.map_rel_iff']
    dsimp
    rw [this, subcomplex_le_boundary_iff]
    intro h'
    apply h
    apply_fun (fun A ↦ A.image f) at h'
    rw [image_top] at h'
    rw [← h']
    simp [iso, OrderIso.symm, subset_orderIso, range_orderIso, subcomplex_orderIso]
    have := toRangeSubcomplex_ι f
    simp_rw [← this]
    rw [image_comp, preimage_image_of_isIso]
    simp [Subcomplex.homOfLE, Subpresheaf.homOfLe]
    ext k x
    simp
    intro a
    apply hA
    exact a

lemma hornProdSubcomplex_le_boundary_iff {a b hab} (A : (Δ[n] ⊗ Δ[2]).Subcomplex) (hA : A ≤ σ a b hab) :
    A ≤ (boundaryProdSubcomplex a b hab) ↔ A ≠ (σ a b hab) :=
  image_le_boundary_iff (f a b hab) _ hA

-- need to add extra lemmas to make this simple
lemma le_horn_image_iff {n} {X : SSet} (f : Δ[n + 1] ⟶ X) [Mono f]
    (A : X.Subcomplex) (hA : A ≤ range f) (i : Fin (n + 2)) :
      A ≤ Λ[n + 1, i].image f ↔ ¬ (face {i}ᶜ).image f ≤ A := by
  let iso := OrderIso.trans (subset_orderIso (range f)).symm (range_orderIso f).symm
  have : iso ⟨Λ[n + 1, i].image f, image_le_range _ _⟩ = Λ[n + 1, i] := helper' _ _
  constructor
  · intro h
    replace h : (⟨A, hA⟩ : {p : X.Subcomplex // p ≤ range f}) ≤
      ⟨Λ[n + 1, i].image f, image_le_range _ _⟩ := h
    rw [← iso.map_rel_iff', RelIso.coe_fn_toEquiv, this, stdSimplex.subcomplex_le_horn_iff] at h
    intro h'
    apply h
    have := preimage_monotone f h'
    dsimp at this
    have g := (preimage_eq_iff f (face {i}ᶜ) ((face {i}ᶜ).image f)).2 (by simp only [image_le_range, inf_of_le_left])
    rw [g] at this
    convert this
    ext
    simp [iso, OrderIso.symm, subset_orderIso, range_orderIso, subcomplex_orderIso,
      Subcomplex.homOfLE, Subpresheaf.homOfLe, toRangeSubcomplex, Subpresheaf.toRange,
      Subpresheaf.lift]
  · intro h
    change (⟨A, hA⟩ : {p : X.Subcomplex // p ≤ range f}) ≤
      ⟨Λ[n + 1, i].image f, image_le_range _ _⟩
    rw [← iso.map_rel_iff']
    dsimp
    rw [this, subcomplex_le_horn_iff]
    intro h'
    apply h
    convert image_monotone f h'
    simp [iso, OrderIso.symm, subset_orderIso, range_orderIso, subcomplex_orderIso]
    have := toRangeSubcomplex_ι f
    simp_rw [← this]
    rw [image_comp, preimage_image_of_isIso]
    simp [Subcomplex.homOfLE, Subpresheaf.homOfLe]
    ext k x
    simp
    intro a
    apply hA
    exact a

lemma le_horn_condition {n} {a b hab} (A : (Δ[n] ⊗ Δ[2]).Subcomplex) (hA : A ≤ σ a b hab) :
    A ≤ hornProdSubcomplex a b hab ↔ ¬ faceProdSubcomplex a.succ (f a b hab) ≤ A :=
  le_horn_image_iff (f a b hab) A hA a.succ

lemma faceProdSubcomplex_succ_not_le_unionProd₁ {n} (b : Fin n) (a : Fin b.1) :
    ¬ faceProdSubcomplex (a.succ : Fin (n + 1)).succ (f a.succ.1 b.castSucc ((Fin.natCast_mono b.is_lt.le a.succ.is_le).trans (by simp)))
      ≤ Subcomplex.prod ⊤ Λ[2, 1] := by
  dsimp [faceProdSubcomplex]
  simp [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff]
  refine Set.nmem_setOf_iff.2 ?_
  simp [horn]
  change insert 1 (Set.range (f₂' (_) b.castSucc ∘ ⇑(SimplexCategory.δ _))) = Set.univ
  simp [ConcreteCategory.hom, SimplexCategory.Hom.toOrderHom, SimplexCategory.σ,
    SimplexCategory.δ, SimplexCategory.Hom.mk, Fin.predAbove, Fin.succAboveOrderEmb]
  ext i
  simp
  fin_cases i
  · simp
    use a.succ
    simp
  · simp
  · simp
    use b.castSucc.succ
    simp [Fin.succAbove]
    split
    · next h =>
      exfalso
      exact h.not_lt (Fin.natCast_strictMono b.2 <| Nat.lt_of_le_of_lt (show a.1 + 1 ≤ b from a.2) (Nat.lt_add_one b))
    · next h =>
      split
      · next h' =>
        exfalso
        apply h
        simp at h'
        exact h'.le
      · next h' =>
        simp
        refine Fin.castSucc_lt_iff_succ_le.mpr (le_of_eq ?_)
        ext
        refine Eq.symm (Fin.val_cast_of_lt (Nat.add_lt_add_right b.2 1))

lemma faceProdSubcomplex_succ_not_le_unionProd₂ {n} (b : Fin n) (a : Fin b.1) :
    ¬ faceProdSubcomplex (a.succ : Fin (n + 1)).succ (f a.succ.1 b.castSucc ((Fin.natCast_mono b.is_lt.le a.succ.is_le).trans (by simp)))
      ≤ ∂Δ[n].prod ⊤ := by
  dsimp [faceProdSubcomplex]
  simp [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary, f]
  change Function.Surjective (((a.succ : Fin (n + 1))).predAbove ∘ ⇑((a.succ : Fin (n + 1))).succ.succAboveOrderEmb)
  simp [Fin.succAboveOrderEmb]
  intro i
  simp [Fin.predAbove, Fin.succAbove]
  use i
  split
  next => aesop
  next h =>
    simp
    intro h'
    exfalso
    exact h h'.le

lemma faceProdSubcomplex_succ_not_le_σij {n} (b : Fin n) (a : Fin b.1) (j : Fin b.1) (i : Fin (j.1 + 1)) :
    ¬ faceProdSubcomplex (a.succ : Fin (n + 1)).succ (f a.succ.1 b.castSucc ((Fin.natCast_mono b.is_lt.le a.succ.is_le).trans (by simp)))
      ≤ σ ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp only [Fin.mk_le_mk]; omega) := by
  simp [σ, face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff, Set.prod]
  intro x h
  simp [f] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp only [stdSimplex, yoneda, CategoryStruct.comp, SimplexCategory.Hom.comp, unop_id,
    SimplexCategory.id_toOrderHom, SimplexCategory.Hom.comp.eq_1, id_eq, eq_mpr_eq_cast,
    Quiver.Hom.unop_op, SimplexCategory.Hom.toOrderHom_mk, cast_eq, SSet.uliftFunctor,
    Functor.comp_obj, SimplexCategory.len_mk, SimplicialObject.whiskering_obj_obj_obj,
    uliftFunctor_obj, Nat.reduceAdd, SSet.yonedaEquiv, yonedaCompUliftFunctorEquiv,
    Opposite.op_unop, Equiv.coe_fn_symm_mk, prod_map_fst, SimplicialObject.whiskering_obj_obj_map,
    uliftFunctor_map, ULift.up.injEq, prod_map_snd] at h₁ h₂
  have h₁' := congrArg OrderHom.toFun (congrArg SimplexCategory.Hom.toOrderHom h₁)
  have h₂' := congrArg OrderHom.toFun (congrArg SimplexCategory.Hom.toOrderHom h₂)
  clear h h₁ h₂
  simp only [SimplexCategory.Hom.mk, SimplexCategory.Hom.toOrderHom, OrderHom.comp, objMk, f₂] at h₁' h₂'
  cases lt_or_eq_of_le (show a.1 + 1 ≤ b from a.2)
  · next h =>
    have h₁' := congr_fun h₁' b
    have h₂' := congr_fun h₂' b
    dsimp [objEquiv, Equiv.ulift] at h₁' h₂'
    change (SimplexCategory.σ _) (x b) = _ at h₁'
    change (if x _ ≤ _ then 0 else if x _ ≤ _ then 1 else 2) = _ at h₂'
    simp only [Fin.val_succ, Fin.isValue] at h₁' h₂'
    simp only [SimplexCategory.len_mk, ConcreteCategory.hom, SimplexCategory.Hom.toOrderHom,
      SimplexCategory.σ, SimplexCategory.mkHom, SimplexCategory.Hom.mk, SimplexCategory,
      OrderHom.coe_mk, Fin.predAbove, Fin.castSucc_mk, SimplexCategory.δ,
      OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, Fin.succ_succAbove_succ,
      Fin.castSucc_lt_succ_iff, Fin.pred_succ, Fin.isValue, Fin.succ_le_castSucc_iff,
      Fin.succ_le_succ_iff] at h₁' h₂'
    have A : ¬ b.castSucc ≤ (a.succ : Fin (n + 1)) := by
      simp
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      simp at h ⊢
      refine Fin.lt_iff_val_lt_val.mpr ?_
      convert h
      exact Fin.val_cast_of_lt (by omega)
    have B : (a.succ : Fin (n + 1)) ≤ b.castSucc := le_of_not_ge A
    dsimp at A B
    simp [Fin.succAbove, A, B, B.not_lt] at h₁' h₂'
    split at h₁'
    · next h' =>
      rw [Fin.pred_eq_iff_eq_succ] at h₁'
      simp [h'.not_le] at h₂'
      rw [h₁'] at h₂'
      apply h₂'.not_lt
      rcases j with ⟨j, hj⟩
      rcases b with ⟨b, hb⟩
      simp [hj]
    · next h' => aesop
  · next h =>
    have : (a.succ : Fin (n + 1)) = b.castSucc := by aesop
    have h₁' := congr_fun h₁' (a.succ : Fin (n + 1))
    have h₂' := congr_fun h₂' (a.succ : Fin (n + 1))
    dsimp [objEquiv, Equiv.ulift] at h₁' h₂'
    change (SimplexCategory.σ _) (x (a.succ : Fin (n + 1))) = _ at h₁'
    change (if x (a.succ : Fin (n + 1)) ≤ _ then 0 else if x (a.succ : Fin (n + 1)) ≤ _ then 1 else 2) = _ at h₂'
    rw [this] at h₁'
    simp at this
    simp [ConcreteCategory.hom, SimplexCategory.Hom.toOrderHom, SimplexCategory] at h₁' h₂'
    simp_rw [this] at h₂' h₁'
    simp [SimplexCategory.σ, SimplexCategory.δ, SimplexCategory.Hom.mk, Fin.predAbove] at h₁'
    split at h₁'
    · next h' =>
      simp [SimplexCategory.σ, SimplexCategory.δ, SimplexCategory.Hom.mk, Fin.predAbove, h'] at h₂'
      aesop
    · next h' =>
      rw [Fin.castPred_eq_iff_eq_castSucc] at h₁'
      rw [h₁'] at h'
      apply h' (Fin.val_lt_of_le i j.2)

lemma faceProdSubcomplex_succ_not_le_σib {n} (b : Fin n) (a : Fin b.1) (i : Fin (a.1 + 1)) :
    ¬ faceProdSubcomplex (a.succ : Fin (n + 1)).succ (f a.succ.1 b.castSucc ((Fin.natCast_mono b.is_lt.le a.succ.is_le).trans (by simp)))
      ≤ σ (i : Fin (n + 1)) b.castSucc (by
        rw [Fin.le_castSucc_iff]
        refine Fin.coe_succ_lt_iff_lt.mp ?_
        simp
        have : i.1 < n + 1 := by omega
        rw [(Nat.mod_eq_iff_lt (Nat.ne_zero_of_lt this)).2 this]
        refine (Fin.natCast_lt_natCast (Nat.le_of_succ_le this) (Nat.le_add_right_of_le b.2)).mpr (i.2.trans <| Nat.add_lt_add_right a.2 1)) := by
  simp [σ, face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff]
  intro x h
  simp [f] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [SSet.yonedaEquiv, yonedaCompUliftFunctorEquiv, stdSimplex, ChosenFiniteProducts.product,
    yoneda, SSet.uliftFunctor, CategoryStruct.comp] at h₁ h₂
  have h₁' := congrArg OrderHom.toFun (congrArg SimplexCategory.Hom.toOrderHom h₁)
  have h₂' := congrArg OrderHom.toFun (congrArg SimplexCategory.Hom.toOrderHom h₂)
  clear h h₁ h₂
  simp only [SimplexCategory.Hom.mk, SimplexCategory.Hom.toOrderHom, OrderHom.comp, objMk, f₂] at h₁' h₂'
  have h₁' := congr_fun h₁' (a.succ : Fin (n + 1))
  have h₂' := congr_fun h₂' (a.succ : Fin (n + 1))
  simp [objEquiv, Equiv.ulift] at h₁' h₂'
  change (SimplexCategory.σ _) (x (a.succ : Fin (n + 1))) = _ at h₁'
  change (if x (a.succ : Fin (n + 1)) ≤ _ then 0 else if x (a.succ : Fin (n + 1)) ≤ b.castSucc.succ then 1 else 2) = _ at h₂'
  simp only [Fin.val_succ, Fin.isValue] at h₁' h₂'

  by_cases h : (i : Fin (n + 1)).castSucc < x (a.succ : Fin (n + 1))
  · simp at h
    simp [h, Fin.pred_eq_iff_eq_succ] at h₁'
    simp [h.not_le, SimplexCategory.δ, SimplexCategory.Hom.mk] at h₂'
    aesop
  · simp at h
    simp [h.not_lt, ConcreteCategory.hom, SimplexCategory.Hom.toOrderHom, SimplexCategory.σ,
      SimplexCategory.δ, SimplexCategory.Hom.mk, Fin.predAbove] at h₁'
    rw [← Fin.castPred_le_iff, h₁'] at h
    apply h.not_lt
    refine Fin.natCast_strictMono ?_ i.2
    exact (show a.1 + 1 ≤ b from a.2).trans b.2.le

/-- for `0 ≤ a < b < n`,  show `((a + 1) + 1)`-th face is not contained in anything -/
lemma faceProdSubcomplex_succ_not_le {n} (b : Fin n) (a : Fin b.1) :
    ¬ faceProdSubcomplex (a.succ : Fin (n + 1)).succ (f a.succ.1 b.castSucc ((Fin.natCast_mono b.is_lt.le a.succ.is_le).trans (by simp)))
      ≤ filtration₂ b a.castSucc := by
  simp [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff, filtration₂,
    filtration₁, unionProd]
  refine ⟨⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, fun j i ↦ ?_⟩, fun i ↦ ?_⟩
  · -- not in `Δ[n] ⨯ Λ[2, 1]`
    simpa [Set.mem_univ, Fin.isValue, true_and, face_singleton_compl, ← image_le_iff,
      image_ofSimplex, ofSimplex_le_iff, Set.prod] using faceProdSubcomplex_succ_not_le_unionProd₁ b a
  · -- not in `∂Δ[n] ⨯ Δ[2]`
    simpa [Set.mem_univ, and_true, face_singleton_compl, ← image_le_iff, image_ofSimplex,
      ofSimplex_le_iff, Set.prod] using faceProdSubcomplex_succ_not_le_unionProd₂ b a
  · -- not in any `σij` for `i ≤ j < b`
    simpa [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff]
      using faceProdSubcomplex_succ_not_le_σij b a j i
  · -- not in any `σib` for any `i < a + 1`
    simpa [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff]
      using faceProdSubcomplex_succ_not_le_σib b a i

/-
for `0 ≤ a < b < n`, the following square

Λ[n + 1, (a + 1) + 1] ---> X(b) ∪ σ0b ∪ ... ∪ σab
        |                             |
        |                             |
        v                             V
    σ(a + 1)b -------> X(b) ∪ σ0b ∪ ... ∪ σab ∪ σ(a + 1)b

need `b < n` because `X(n)` is the last term. `X(n-1, n-1) = X(n)`.
need `a < b` because we need `a + 1 ≤ b`
e.g. the last square looks like
Λ[n + 1, n] ---> X(n-1) ∪ σ0(n-1) ∪ ... ∪ σ(n-2)(n-1) = X(n-1, n-2)
     |                             |
     |                             |
     v                             V
 σ(n-1)(n-1) -------------------> X(n) = X(n-1, n-1)
-/
def mySq {n} (b : Fin n) (a : Fin b.1) :
    Sq
      (hornProdSubcomplex a.succ.1 b.castSucc ((Fin.natCast_mono b.is_lt.le a.succ.is_le).trans (by simp)))
      (σ a.succ.1 b.castSucc ((Fin.natCast_mono b.is_lt.le a.succ.is_le).trans (by simp)))
      (filtration₂ b a.castSucc)
      (filtration₂ b a.succ)
      where
  max_eq := by
    rw [filtration₂_succ n b a, sup_comm]
    simp only [Fin.coe_eq_castSucc]
  min_eq := by
    apply le_antisymm
    · refine (le_horn_condition _ (inf_le_left.trans (le_of_eq rfl))).2 ?_
      · rw [le_inf_iff, not_and]
        intro h' h
        exact (faceProdSubcomplex_succ_not_le b a) h
    · apply le_inf (le_of_eq_of_le' rfl (hornProdSubcomplex_le_σ _ _ _))
      · exact hornProdSubcomplex_le_filt b a

variable (b : Fin n) (a : Fin b.1)

#check Subcomplex.isColimitPushoutCoconeOfPullback (f a.succ.1 b.castSucc ((Fin.natCast_mono b.is_lt.le a.succ.is_le).trans (by simp)))
  (filtration₂ b a.castSucc) (filtration₂ b a.succ) (Λ[n + 1, a + 2]) ⊤

noncomputable
def mono_iso {S T : SSet} (f : S ⟶ T) [h : Mono f] : S ≅ (range f).toSSet where
  hom := {
    app n x := ⟨f.app n x, ⟨x, rfl⟩⟩
    naturality n m g := by
      ext
      simp
      congr
      apply FunctorToTypes.naturality }
  inv := {
    app n x := x.2.choose
    naturality n m g := by
      ext x
      apply (mono_iff_injective (f.app m)).1 (((NatTrans.mono_iff_mono_app f).1 h) m)
      dsimp
      let a := ((range f).toPresheaf.map g x).property
      rw [a.choose_spec, ← types_comp_apply (S.map g) (f.app m),
        congr_fun (f.naturality g) x.property.choose, types_comp_apply, x.property.choose_spec]
      rfl
    }
  hom_inv_id := by
    ext n x
    apply (mono_iff_injective _).1 (((NatTrans.mono_iff_mono_app _).1 h) n)
    exact Exists.choose_spec (Set.mem_range_self x)
  inv_hom_id := by
    ext n x
    simp
    congr
    exact x.2.choose_spec
