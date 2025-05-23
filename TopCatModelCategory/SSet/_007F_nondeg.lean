import TopCatModelCategory.SSet._007F_filtration
import Mathlib.Data.Sigma.Order

open CategoryTheory MonoidalCategory SSet Simplicial SimplexCategory prodStdSimplex

variable {n : ℕ}

def τ.objMk (i : Σₗ (b : Fin (n + 1)), Fin b.succ) : Δ[2] _⦋n + 2⦌  :=
  stdSimplex.objMk {
    toFun k :=
      if k ≤ (⟨i.2, by omega⟩ : Fin (n + 3)) then 0
      else if k ≤ i.1.castSucc.succ then 1
      else 2
    monotone' := by
      refine Fin.monotone_iff_le_succ.mpr ?_
      rintro (j : Fin (n + 2))
      split
      · next h => simp
      · next h =>
        have : ¬j.succ ≤ ⟨i.2, by omega⟩ := fun h' ↦ h (le_trans (Fin.castSucc_le_succ j) h')
        simp [this]
        split
        · next => aesop
        · next h =>
          have : ¬j ≤ i.1.castSucc := fun h' ↦ h (le_trans (Fin.castSucc_le_castSucc_iff.2 h') (Fin.castSucc_le_succ i.1.castSucc))
          simp [this] }

def σ.objMk (i : Σₗ (b : Fin n), Fin b.succ) : Δ[2] _⦋n + 1⦌  :=
  stdSimplex.objMk {
    toFun k :=
      if k ≤ (⟨i.2, by omega⟩ : Fin (n + 1)) then 0
      else if k ≤ i.1.succ then 1
      else 2
    monotone' := by
      refine Fin.monotone_iff_le_succ.mpr ?_
      rintro (j : Fin (n + 1))
      split
      · next h => simp
      · next h =>
        have : ¬j.succ ≤ ⟨i.2, by omega⟩ := by
          intro h'
          rw [Fin.coe_eq_castSucc] at h
          exact h (le_trans (Fin.castSucc_le_succ j) h')
        simp [this]
        split
        · next =>
          simp at h
          simp_all only [Fin.val_succ, not_le, Fin.isValue]
          split
          next
            h_2 =>
            simp_all only [Fin.isValue, Fin.le_zero_iff, len_mk, Nat.reduceAdd, Fin.one_eq_zero_iff,
              OfNat.ofNat_ne_one]
            have := lt_of_le_of_lt h_2 h
            apply this.not_le
            exact Fin.castSucc_le_succ j
          next h_2 =>
            simp_all only [not_le, Fin.isValue]
            split
            next h_3 => simp_all only [Fin.isValue, le_refl]
            next h_3 => simp_all only [not_le, Fin.isValue, Fin.reduceLE]
        · next h =>
          rename_i q
          have : ¬j.succ ≤ i.1.succ := by
            simp_all
            apply lt_trans h ?_
            exact Fin.castSucc_lt_succ j
          dsimp at this
          simp [this]
          simp_all only [len_mk, Fin.val_succ, not_le, Fin.isValue]
          split
          next h_2 =>
            simp_all only [Fin.isValue, Fin.le_zero_iff, len_mk, Nat.reduceAdd, Fin.reduceEq]
            have := lt_of_le_of_lt h_2 q
            apply this.not_le
            exact Fin.castSucc_le_succ j
          next h_2 => simp_all only [not_le, Fin.isValue, le_refl] }

lemma σ.objMk_injective : Function.Injective (σ.objMk (n := n)) := by
  intro i j h
  rcases i with ⟨b, a⟩
  rcases j with ⟨b', a'⟩
  dsimp [σ.objMk] at h
  wlog hb : b < b' generalizing b b'
  · simp only [not_lt] at hb
    obtain hb | rfl := hb.lt_or_eq
    · exact (this _ _ _ _ h.symm hb).symm
    · clear hb
      wlog ha : a < a' generalizing a a'
      · simp only [not_lt] at ha
        obtain ha | rfl := ha.lt_or_eq
        · exact (this _ _ h.symm ha).symm
        · rfl
      have := stdSimplex.objMk_injective h
      simp at this
      have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨a', by dsimp; omega⟩
      simp [Fin.le_iff_val_le_val] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      simp [ha.not_le] at this
  exfalso
  have := stdSimplex.objMk_injective h
  simp at this
  have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨b'.succ, by dsimp; omega⟩
  simp at this
  have p : ¬ b'.1 + 1 ≤ a.1 := by
    simp only [Fin.val_succ, not_le]
    rw [Fin.lt_iff_val_lt_val] at hb
    omega
  have p' : ¬ b'.1 + 1 ≤ a'.1 := by dsimp; omega
  have p'' : ⟨b'.1 + 1, by omega⟩ ≤ b'.castSucc.succ := by
    rw [Fin.le_iff_val_le_val]
    simp
  simp [Fin.le_iff_val_le_val] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  simp [p, p', p''] at this
  omega

lemma τ.objMk_injective : Function.Injective (τ.objMk (n := n)) := by
  intro i j h
  rcases i with ⟨b, a⟩
  rcases j with ⟨b', a'⟩
  dsimp [τ.objMk] at h
  wlog hb : b < b' generalizing b b'
  · simp only [not_lt] at hb
    obtain hb | rfl := hb.lt_or_eq
    · exact (this _ _ _ _ h.symm hb).symm
    · clear hb
      wlog ha : a < a' generalizing a a'
      · simp only [not_lt] at ha
        obtain ha | rfl := ha.lt_or_eq
        · exact (this _ _ h.symm ha).symm
        · rfl
      have := stdSimplex.objMk_injective h
      simp at this
      have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨a', by dsimp; omega⟩
      simp [ha] at this
      exfalso
      aesop
  exfalso
  have := stdSimplex.objMk_injective h
  simp at this
  have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨b'.succ, by dsimp; omega⟩
  simp at this
  have p : ¬ b'.1 + 1 ≤ a.1 := by
    simp only [Fin.val_succ, not_le]
    rw [Fin.lt_iff_val_lt_val] at hb
    omega
  have p' : ¬ b'.1 + 1 ≤ a'.1 := by dsimp; omega
  have p'' : ⟨b'.1 + 1, by omega⟩ ≤ b'.castSucc.succ := by
    rw [Fin.le_iff_val_le_val]
    simp
  simp [p, p', p''] at this
  rw [Fin.le_iff_val_le_val] at this
  simp at this
  omega

lemma τ.objMk_surjective : Function.Surjective (τ.objMk (n := n)) := sorry

instance (b : Fin (n + 1)) : OrderTop (Fin b.succ) where
  top := ⟨b, Nat.lt_add_one b⟩
  le_top a := Nat.le_of_lt_succ a.isLt

lemma _root_.Sigma.Fin_top_eq :
    (⊤ : Σₗ (b : Fin (n + 1)), Fin b.succ) = ⟨Fin.last n, Fin.last n⟩ := rfl

def τ' (i : Σₗ (b : Fin (n + 1)), Fin b.succ) : (Δ[n] ⊗ Δ[2] : SSet) _⦋n + 2⦌ :=
  (stdSimplex.objEquiv.symm (σ (⟨i.2, by omega⟩ : Fin (n + 2)) ≫ σ i.1), τ.objMk i)

/-- for all `0 ≤ a ≤ b ≤ n`, we get a nondegenerate `(n+2)`-simplex. -/
def τ.nonDegenerateEquiv.toFun (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 2) := by
  refine ⟨τ' i, ?_⟩
  rcases i with ⟨b, a⟩
  rw [objEquiv_nonDegenerate_iff, Fin.orderHom_injective_iff]
  intro j h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  clear h
  simp [τ', objEquiv, stdSimplex.objMk, SimplexCategory.σ, τ.objMk, Fin.predAbove] at h₁ h₂
  split at h₂
  · next h =>
    simp [h.not_lt] at h₁
    split at h₂
    · next h' =>
      simp [h'.not_lt] at h₁
      have : j ≤ b := by
        rw [← Fin.castSucc_le_castSucc_iff]
        refine le_trans h ?_
        rw [Fin.le_iff_val_le_val]
        dsimp
        rw [Nat.mod_eq_of_lt]
        all_goals omega
      simp_rw [Fin.lt_castPred_succ_iff] at h₁
      split at h₁
      · next h' =>
        simp [h'.le] at h₁
        rw [h₁] at this
        rw [Fin.castpred_succ_le_iff] at this
        have := h'.trans this
        apply this.not_le
        rw [Fin.le_iff_val_le_val]
        simp
      · next h'' =>
        simp at h''
        cases (lt_or_eq_of_le h'')
        · next h'' =>
          simp [h''.not_le] at h₁
          refine (Fin.lt_castPred_succ ?_).not_le h₁.symm.le
          simp
          intro H
          rw [H] at h''
          rw [Fin.lt_iff_val_lt_val] at h''
          simp at h''
          omega
        · next h' =>
          clear h₁
          subst h'
          apply h'.not_lt
          rw [Fin.lt_iff_val_lt_val]
          simp
    · next h' => aesop
  · next h =>
    simp_all only [not_le, dite_true, eq_mp_eq_cast, id_eq]
    have : ⟨a, by omega⟩ < j.succ := h.trans (Fin.castSucc_lt_succ j)
    simp [this, this.not_le] at h₁ h₂
    split at h₁
    · next h' =>
      rw [Fin.lt_pred_iff] at h'
      simp [h'.not_le] at h₂
      split at h₁
      next h_2 =>
        split at h₂
        next h_3 => simp_all only [Fin.pred_inj, Fin.isValue, Fin.reduceEq]
        next h_3 =>
          simp_all only [Fin.pred_inj, not_le, Fin.isValue]
          simp_all only [Fin.val_succ]
          have := Fin.pred_castSucc_lt (Fin.castSucc_ne_zero_of_lt h_2)
          simp_all only [lt_self_iff_false]
      next h_2 =>
        split at h₂
        all_goals omega
    · next h' =>
      split at h₂
      next h_2 =>
        split at h₁
        next h_3 =>
          split at h₂
          all_goals omega
        next h_3 =>
          split at h₂
          next h_4 =>
            have := Fin.pred_castSucc_lt (Fin.ne_zero_of_lt h)
            simp_all
          next h_4 => omega
      next h_2 =>
        split at h₁
        next h_3 =>
          split at h₂
          next h_4 => omega
          next h_4 =>
            simp_all
            clear h₁
            rcases a with ⟨a, ha⟩
            rcases b with ⟨b, hb⟩
            rcases j with ⟨j, hj⟩
            simp_all
            rw [Fin.pred_le_iff] at h'
            simp at h'
            apply h_2.not_le h'
        next h_3 =>
          split at h₂
          all_goals omega

noncomputable
def τ.nonDegenerateEquiv :
    (Σₗ (b : Fin (n + 1)), Fin b.succ) ≃ (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 2) := by
  refine Equiv.ofBijective (τ.nonDegenerateEquiv.toFun) ?_
  constructor
  · intro i j h
    simpa using τ.objMk_injective (congr_arg (Prod.snd ∘ Subtype.val) h)
  ·
    sorry

namespace τ

noncomputable abbrev simplex (j : Σₗ (b : Fin (n + 1)), Fin b.succ) := nonDegenerateEquiv j

noncomputable abbrev ιSimplex (j : Σ (b : Fin (n + 1)), Fin b.succ) :
    (Δ[n + 2] : SSet) ⟶ Δ[n] ⊗ Δ[2] :=
  SSet.yonedaEquiv.symm (simplex j)

instance (j : Σ (b : Fin (n + 1)), Fin b.succ) : Mono (ιSimplex j) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1 (nonDegenerateEquiv j).2

open Subcomplex in
noncomputable
def filtration₂ (j : Σₗ (b : Fin (n + 1)), Fin b.succ) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (unionProd (boundary n) (horn 2 1)) ⊔
    (⨆ (i : Σₗ (b : Fin (n + 1)), Fin b.succ) (_ : i < j), ofSimplex (simplex i).1)

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
  obtain ⟨i, hi⟩ := nonDegenerateEquiv.surjective ⟨x, hx⟩
  obtain rfl : simplex i = x := by simp_all only [simplex, Fin.val_succ]
  rw [filtration₂, ← Subcomplex.ofSimplex_le_iff]
  refine le_sup_of_le_right (le_iSup₂_of_le i ?_ (le_refl _))
  sorry

end τ
