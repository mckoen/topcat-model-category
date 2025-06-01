import TopCatModelCategory.SSet._007F_filtration
import TopCatModelCategory.SSet._Order

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

open Subcomplex stdSimplex

variable {n : ℕ} (a b : Fin (n + 1))

namespace τ

/-- for `0 ≤ a ≤ b ≤ n`, the image of `Λ[n + 2, a + 1]` under `g a b : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
abbrev innerHornImage : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (horn (n + 2) a.succ.castSucc).image (g a b)

/-- the image of the `i`-th face of `Δ[n + 2]` under some map `Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
abbrev faceImage (i : Fin (n + 3)) (f : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (face {i}ᶜ).image f

lemma innerHornImage_eq_iSup : innerHornImage a b =
    ⨆ (j : ({a.succ.castSucc}ᶜ : Set (Fin (n + 3)))), faceImage j.1 (g a b) := by
  simp only [innerHornImage, horn_eq_iSup, image_iSup, faceImage]

lemma innerHornImage_le : innerHornImage a b ≤ τ a b := by
  rw [innerHornImage_eq_iSup]
  exact iSup_le fun _ ↦ image_le_range _ (g a b)

lemma faceImage_le (j : Fin (n + 3)) :
    faceImage j (g a b) ≤ τ a b := image_le_range _ _

/-- for `0 ≤ a ≤ b ≤ n`, each face of `τ a b` except the `a`-th, `(a+1)`-th, `(b+1)`-th, and
  `(b+2)`-th is contained in `∂Δ[n] ⊗ Δ[2]`. -/
lemma faceImage_le_boundary_prod_top (hab : a ≤ b) (j : Fin (n + 3))
    (ha : ¬j = a.castSucc.castSucc) (ha' : ¬j = a.succ.castSucc)
    (hb : ¬j = b.succ.castSucc) (hb' : ¬j = b.succ.succ) :
      faceImage j (g a b) ≤ (boundary n).prod ⊤ := by
  simp [face_singleton_compl]
  refine ⟨?_, Set.mem_univ _⟩
  change ¬Function.Surjective (Fin.predAbove _ ∘ Fin.predAbove _ ∘ Fin.succAbove _)
  intro h
  have : j < a.castSucc.castSucc ∨ a.succ.castSucc < j := by
    cases Fin.lt_or_lt_of_ne ha
    all_goals cases Fin.lt_or_lt_of_ne ha'; try omega
    any_goals omega
    · next q q' =>
      exfalso
      exact not_le.2 q' q
  cases this
  · next hj =>
    obtain ⟨i, hi⟩ := h ⟨j, lt_trans hj (by simp)⟩
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj
    split at hi
    · next h' =>
      simp [show ¬a.1 < i.1 by omega, show ¬b.1 < i by omega, Fin.eq_mk_iff_val_eq] at hi
      omega
    · next h' =>
      split at hi
      all_goals
        simp [Fin.eq_mk_iff_val_eq] at hi
        · next h'' =>
          split at hi
          all_goals
            simp at hi h''
            omega
  · next hj =>
    have : j < b.succ.castSucc ∨ b.succ.succ < j := by
      cases Fin.lt_or_lt_of_ne hb'
      all_goals cases Fin.lt_or_lt_of_ne hb; try omega
      any_goals omega
      · next q q' =>
        exfalso
        exact not_lt.2 q' q
    cases this
    . next hj' =>
      simp [Fin.lt_iff_val_lt_val] at hj hj'
      obtain ⟨i, hi⟩ := h ⟨j - 1, by dsimp; omega⟩
      simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj hj'
      split at hi
      · next h' =>
        split at hi
        · next =>
          simp [show ¬b.1 < i - 1 by omega, Fin.eq_mk_iff_val_eq] at hi
          omega
        · next h'' =>
          simp [show ¬b.1 < i by omega, Fin.eq_mk_iff_val_eq] at hi
          simp_all
          omega
      · next h'' =>
        simp [show a.1 < i + 1 by omega] at hi
        split at hi
        all_goals
          simp [Fin.eq_mk_iff_val_eq] at hi
          omega
    · next hj' =>
      simp [Fin.lt_iff_val_lt_val] at hj hj'
      obtain ⟨i, hi⟩ := h ⟨j - 2, by dsimp; omega⟩
      simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj hj'
      split at hi
      · next h' =>
        split at hi
        · next h'' =>
          split at hi
          all_goals
            simp [Fin.eq_mk_iff_val_eq] at hi
            simp_all
            omega
        · next h'' =>
          split at hi
          all_goals
            simp [Fin.eq_mk_iff_val_eq] at hi
            simp_all
          simp_all
          omega
          omega
      · next h'' =>
        simp [show a.1 < i + 1 by omega] at hi
        split at hi
        all_goals
          simp [Fin.eq_mk_iff_val_eq] at hi
          omega

/-- for `0 ≤ a ≤ b < n` the `(b + 2)`-th face of `τ a b` is `σ a b`. -/
lemma faceImage_b_succ_succ_eq (hab : a ≤ b) (hn : b < Fin.last n) :
    faceImage b.succ.succ (g a b) = σ ⟨a, by omega⟩ ⟨b, by omega⟩ := by
  simp [face_singleton_compl, σ, f, g, f₂, range, Subpresheaf.range_eq_ofSection', SSet.yonedaEquiv,
    SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex, objEquiv, SimplexCategory.σ,
    SimplexCategory.δ, objMk]
  congr
  apply Prod.ext
  all_goals
    simp [Equiv.ulift]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
  · change (b.predAbove ∘ a.castSucc.predAbove) ∘ b.succ.succ.succAbove = a.predAbove
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val]
    split
    · simp
      split
      · simp [show ¬b.1 < e - 1 by omega]
      · next h' => simp [((not_lt.1 h').trans hab).not_lt]
    · simp [show a.1 < e + 1 by omega, show b.1 < e by omega, show a.1 < e by omega]
  · change f₂' a b ∘ b.succ.succ.succAbove = f₂' ⟨a, by omega⟩ ⟨b, by omega⟩
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    split
    · aesop
    · simp [show ¬e.1 + 1 ≤ a by omega, show ¬e.1 ≤ b by omega, show ¬e.1 ≤ a by omega,
        show ¬e.1 ≤ b + 1 by omega]

/-- for `0 ≤ a ≤ n` the `(n + 2)`-th face of `τ a n` is contained in `Δ[n] ⊗ Λ[2, 1]`. -/
lemma faceImage_last_le_top_prod_horn :
    faceImage (Fin.last (n + 2)) (g a (Fin.last n)) ≤ (⊤ : Subcomplex Δ[n]).prod (horn 2 1) := by
  simp [face_singleton_compl, SimplexCategory.δ, Fin.succAboveOrderEmb]
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (f₂' a (Fin.last n) ∘ Fin.castSucc) ∪ {1} ≠ Set.univ
  intro h'
  rw [Set.eq_univ_iff_forall] at h'
  have h'' := h' 2
  simp at h''
  obtain ⟨e, he⟩ := h''
  by_cases h : a.castSucc < e
  · simp [h.not_le, Fin.lt_iff_val_lt_val] at he
    omega
  · aesop

/-- for `0 ≤ a ≤ b < n` the `((b + 1) + 1)`-th face of `τ a (b + 1)` is `σ a b`. -/
lemma faceImage_b_succ_eq (n : ℕ) (b : Fin n) (a : Fin b.succ) :
    faceImage ⟨b.succ.succ, by omega⟩ (g ⟨a, by omega⟩ b.succ) = σ ⟨a, by omega⟩ b := by
  simp [face_singleton_compl, σ, f, g, f₂, range, Subpresheaf.range_eq_ofSection', SSet.yonedaEquiv,
    SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex, objEquiv, SimplexCategory.σ,
    SimplexCategory.δ, objMk]
  congr
  apply Prod.ext
  all_goals
    simp [Equiv.ulift]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
  · simp
    change (Fin.predAbove _ ∘ Fin.predAbove _) ∘ Fin.succAbove _ = Fin.predAbove _
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val]
    split
    · next h =>
      simp
      split
      · simp [show ¬b.1 + 1 < e - 1 by omega]
        split
        · aesop
        · next h'' =>
          rw [Nat.mod_eq_of_lt (by omega)] at h''
          omega
      · simp [show ¬b.1 + 1 < e by omega]
        split
        · next h'' =>
          rw [Nat.mod_eq_of_lt (by omega)] at h''
          omega
        · aesop
    · next h =>
      simp [show a.1 < e + 1 by dsimp; omega, show a.1 < e by dsimp; omega]
      split
      · split
        · aesop
        · next h' =>
          rw [Nat.mod_eq_of_lt (by omega)] at h'
          omega
      · omega
  · change f₂' ⟨a, _⟩ b.succ ∘ Fin.succAbove _ = f₂' ⟨a, by omega⟩ b
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    split
    · next h => simp [h.le, show e.1 ≤ b + 1 by omega]
    · simp [show ¬e.1 + 1 ≤ a by dsimp; omega, show ¬e.1 ≤ a by dsimp; omega]

/-- for `0 ≤ b ≤ n`, the `0`-th face of `τ 0 b` is contained in `Δ[n] ⊗ Λ[2, 1]`. -/
lemma faceImage_zero_le_top_prod_horn :
    faceImage 0 (g 0 b) ≤ (⊤ : Subcomplex Δ[n]).prod (horn 2 1) := by
  simp [face_singleton_compl]
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (f₂' ⟨0, by omega⟩ b ∘ Fin.succ) ∪ {1} ≠ Set.univ
  intro h'
  rw [Set.eq_univ_iff_forall] at h'
  have h'' := h' 0
  simp at h''
  obtain ⟨e, he⟩ := h''
  have := he e.succ_ne_zero
  aesop

/-- for `0 ≤ a < b ≤ n` the `(a + 1)`-th face of `τ (a + 1) b` is the `(a + 1)`-th face of
  `τ a b`. -/
lemma faceImage_succ_eq (hab : a < b) :
    faceImage a.succ.castSucc (g ⟨a.succ, by dsimp; omega⟩ b) =
      faceImage a.succ.castSucc (g a b) := by
  simp [face_singleton_compl]
  congr
  apply Prod.ext
  all_goals
    simp [g, f₂, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, objMk]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Nat.mod_eq_of_lt]
  · split
    · next h => simp [h.le.not_lt, show (¬ a.1 < e) by omega]
    · next => simp [show (a.1 < e) by omega, show (a.1 < e + 1) by omega]
  · split
    · next h => simp [h.le, show e.1 ≤ a by omega]
    · next =>
      simp [show ¬e.1 ≤ a by omega]
      split
      all_goals simp [show ¬e.1 + 1 ≤ a by omega]

/-- for `0 ≤ a < b ≤ n`, the `(a + 1)`-th face of `τ (a + 1) b` is contained in `τ a b`. -/
lemma faceImage_succ_le (hab : a < b) :
    faceImage a.succ.castSucc (g ⟨a.succ, by simp; omega⟩ b) ≤ τ a b := by
  rw [faceImage_succ_eq a b hab]
  exact faceImage_le _ _ _

/-
/-- for `0 ≤ a < b ≤ n`, the image of `Λ[n + 2, (a + 1) + 1]` under `g a b` is contained
  in `X(b, a)`. -/
lemma innerHornImage_succ_le_filtration₄ (n : ℕ) (b : Fin (n + 1)) (a : Fin b) (hn : b.succ < Fin.last (n + 1)):
    innerHornImage (n := n + 1) ⟨a.succ, by omega⟩ b.succ
      ≤ filtration₄ b.succ ⟨a, by simp; omega⟩ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = ⟨a.succ, by omega⟩
  · subst h
    refine le_sup_of_le_right (le_iSup_of_le ⟨a, Nat.lt_add_one a⟩ ?_)
    exact faceImage_succ_le ⟨a, by omega⟩ b.succ (by simp [Fin.lt_iff_val_lt_val]; omega)
  · apply le_sup_of_le_left (le_sup_of_le_left ?_)
    by_cases h' : j = b.succ.succ.succ
    · subst h'
      rw [faceImage_b_succ_succ_eq _ b.succ (by simp [Fin.le_iff_val_le_val]) hn]
      exact le_sup_of_le_right
        (le_iSup₂_of_le ⟨b.succ, by simp [Fin.lt_iff_val_lt_val] at hn ⊢; omega⟩ ⟨a.succ, by simp; omega⟩ le_rfl)
    by_cases h'' : j = b.castSucc.succ.succ
    · subst h''
      have := faceImage_b_succ_eq ⟨a.succ, by omega⟩ b.castSucc
        (by simp [Fin.le_iff_val_le_val]; omega) (by simp [Fin.lt_iff_val_lt_val])
      simp [Fin.succ] at this ⊢
      rw [this]
      exact le_sup_of_le_right (le_iSup₂_of_le b ⟨a.succ, by simp⟩ (le_refl _))
    · exact le_sup_of_le_left (le_sup_of_le_right
        (faceImage_le_boundary_prod_top ⟨a.succ, by omega⟩ b.succ
          (by simp [Fin.le_iff_val_le_val]) j h hj h'' h'))
-/

/-- for `0 ≤ a < b < n`, the image of `Λ[n + 2, (a + 1) + 1]` under `g (a + 1) (b + 1)` is contained
  in `X(b + 1, a)`. -/
lemma innerHornImage_succ_le_filtration₄' {n : ℕ} (b : Fin n) (a : Fin b) :
    innerHornImage ⟨a.succ, by omega⟩ b.succ
      ≤ filtration₄ b.succ ⟨a, by simp; omega⟩ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = ⟨a.succ, by omega⟩
  · subst h
    refine le_sup_of_le_right (le_iSup_of_le ⟨a, Nat.lt_add_one a⟩ ?_)
    exact faceImage_succ_le ⟨a, by omega⟩ b.succ (by simp [Fin.lt_iff_val_lt_val]; omega)
  · apply le_sup_of_le_left (le_sup_of_le_left ?_)
    have := faceImage_le_boundary_prod_top ⟨a.succ, by omega⟩ b.succ (by simp [Fin.le_iff_val_le_val]) j h hj
    by_cases h' : j = b.succ.succ.castSucc
    · subst h'
      rw [faceImage_b_succ_succ_eq _ b.castSucc (by simp [Fin.le_iff_val_le_val]; omega)
        (by simp [Fin.lt_iff_val_lt_val])]
      exact le_sup_of_le_right
        (le_iSup₂_of_le ⟨b', by simp⟩ ⟨a.succ, by simp⟩ le_rfl)
    by_cases h'' : j = b'.castSucc.succ.castSucc
    · subst h''
      have := faceImage_b_succ_eq n b' ⟨a.succ, by dsimp; omega⟩
      sorry
      --simp [Fin.succ] at this ⊢
      --rw [this]
      --exact le_sup_of_le_right (le_iSup₂_of_le b ⟨a.succ, by simp⟩ (le_refl _))

    sorry
    /-
    cases Fin.eq_last_or_eq_castSucc b
    · next hb =>
      subst hb
      by_cases h' : j = Fin.last (n + 2)
      · subst h'
        apply le_sup_of_le_left
          (le_sup_of_le_left (faceImage_last_le_top_prod_horn ⟨a.succ, by omega⟩))
      ·
        sorry
    · next hb =>
      obtain ⟨b', hb'⟩ := hb
      subst hb'
      by_cases h' : j = b'.castSucc.succ.succ
      · subst h'
        rw [faceImage_b_succ_succ_eq _ b'.castSucc (by simp [Fin.le_iff_val_le_val]; omega)
          (by simp [Fin.lt_iff_val_lt_val])]
        exact le_sup_of_le_right
          (le_iSup₂_of_le ⟨b', by simp⟩ ⟨a.succ, by simp⟩ le_rfl)
      by_cases h'' : j = b'.castSucc.succ.castSucc
      · subst h''
        have := faceImage_b_succ_eq n b' ⟨a.succ, by dsimp; omega⟩
        sorry
        --simp [Fin.succ] at this ⊢
        --rw [this]
        --exact le_sup_of_le_right (le_iSup₂_of_le b ⟨a.succ, by simp⟩ (le_refl _))
      sorry
      -/

end τ

/-- a subcomplex `A` of `Δ[n] ⊗ Δ[2]` which is contained in `τ a b` is contained in the image of
  `Λ[n + 2, a + 1]` under `g a b` iff the `(a + 1)`-th face of `τ a b` is not contained in `A`. -/
lemma subcomplex_le_innerHornImage_iff {a b : Fin (n + 1)} (ha : a ≤ b)
    (A : (Δ[n] ⊗ Δ[2]).Subcomplex) (hA : A ≤ τ a b) :
    A ≤ τ.innerHornImage a b ↔ ¬ τ.faceImage a.succ.castSucc (g a b) ≤ A :=
  letI := g_mono a b ha
  subcomplex_le_horn_image_iff (g a b) A hA a.succ.castSucc

/-
for `0 ≤ a < b ≤ n`, (so for `n ≥ 1`) the following square

`Λ[n+2,(a+1)+1]` -------> `Y(b) ∪ τ0b ∪ ... ∪ τab`
        |                             |
        |                             |
        v                             V
    `τ(a+1)b` ------> `Y(b) ∪ τ0b ∪ ... ∪ τab ∪ τ(a+1)b`

so this says `X(b,a) ↪ X(b,a+1)` is inner anodyne

need `b ≤ n` because `Y(n + 1)` is the last term. `Y(n, n) = X(n + 1)`.
need `a < b` because we need `a + 1 ≤ b`
-/
def filtrationPushout_intermediate (n : ℕ) (a : Fin b) :
    Sq
      (τ.innerHornImage ⟨a.succ, by omega⟩ b)
      (τ ⟨a.succ, by omega⟩ b)
      (filtration₄ b a.castSucc)
      (filtration₄ b a.succ)
      where
  max_eq := by rw [filtration₄_succ b a, sup_comm]
  min_eq := by
    apply le_antisymm
    · rw [subcomplex_le_innerHornImage_iff (by simp [Fin.le_iff_val_le_val]; omega) _ inf_le_left, le_inf_iff, not_and]
      exact fun _ ↦ sorry --(τ.faceImage_succ_not_le_filtration₄ b a)
    · exact le_inf (τ.innerHornImage_le _ _) sorry --(τ.innerHornImage_succ_le_filtration₄ _ _)
