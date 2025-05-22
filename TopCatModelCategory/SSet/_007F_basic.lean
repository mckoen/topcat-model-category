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
