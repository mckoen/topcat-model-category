import TopCatModelCategory.SSet._007F_filtration
import TopCatModelCategory.SSet._Order

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

open Subcomplex stdSimplex

variable {n : ℕ} (a b : Fin (n + 1))

namespace τ

/-- for `0 ≤ a ≤ b ≤ n`, the image of `Λ[n + 2, a + 1]` under `gab : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
def innerHornImage : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (horn (n + 2) a.succ.castSucc).image (g a b)

/-- for `0 ≤ a ≤ b ≤ n`, the image of `∂Δ[n + 2]` under `gab : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
def boundaryImage : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (boundary (n + 2)).image (g a b)

/-- image of the `i`-th face under some `f : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
def faceImage (i : Fin (n + 3)) (f : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (face {i}ᶜ).image f

lemma innerHornImage_eq_iSup : innerHornImage a b =
    ⨆ (j : ({a.succ.castSucc}ᶜ : Set (Fin (n + 3)))), faceImage j.1 (g a b) := by
  simp only [innerHornImage, horn_eq_iSup, image_iSup, faceImage]

lemma boundaryImage_eq_iSup : boundaryImage a b =
    ⨆ (j : Fin (n + 3)), faceImage j.1 (g a b) := by
  simp only [boundaryImage, boundary_eq_iSup, image_iSup, faceImage, Fin.cast_val_eq_self]

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

/-- for `0 ≤ a ≤ b < n` the `((b + 1) + 1)`-th face of `τ a (b + 1)` is `σ a b`. -/
lemma faceImage_b_succ_eq (hab : a ≤ b) (hn : b < n) :
    faceImage b.succ.succ (g a ⟨b + 1, by omega⟩) = σ ⟨a, by omega⟩ ⟨b, by omega⟩ := by
  simp [face_singleton_compl, σ, f, g, f₂, range, Subpresheaf.range_eq_ofSection', SSet.yonedaEquiv,
    SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex, objEquiv, SimplexCategory.σ,
    SimplexCategory.δ, objMk]
  congr
  apply Prod.ext
  all_goals
    simp [Equiv.ulift]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
  · simp
    change (Fin.predAbove _ ∘ a.castSucc.predAbove) ∘ b.succ.succ.succAbove = a.predAbove
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val]
    split
    · next h =>
      simp
      split
      · simp [show ¬b.1 + 1 < e - 1 by omega]
      · simp [show ¬b.1 + 1 < e by omega]
    · next h =>
      simp [show a.1 < e + 1 by omega, show a.1 < e by omega]
      split
      · aesop
      · omega
  · change f₂' a ⟨b + 1, _⟩ ∘ b.succ.succ.succAbove = f₂' ⟨a, by omega⟩ ⟨b, by omega⟩
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    split
    · next h => simp [h.le, show e.1 ≤ b + 1 by omega]
    · simp [show ¬e.1 + 1 ≤ a by omega, show ¬e.1 ≤ a by omega]

/-- the `0`-th face of `τ 0 b` is contained in `Δ[n] ⊗ Λ[2, 1]`. -/
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

/-- for `0 ≤ a ≤ n` the `(n + 2)`-th face of `τ a n` is contained in `Δ[n] ⊗ Λ[2, 1]`. -/
lemma faceImage_last_le_top_prod_horn :
    faceImage (Fin.last (n + 2)) (g a n) ≤ (⊤ : Subcomplex Δ[n]).prod (horn 2 1) := by
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

section a_lt_b

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

end a_lt_b

/-- for `0 ≤ a < b < n`, the image of `Λ[n + 1, (a + 1) + 1]` under `f a b` is contained
  in `X(b, a)`. -/
lemma innerHornImage_succ_le_filtration₄ (a : Fin b) :
    innerHornImage ⟨a.succ, by omega⟩ b
      ≤ filtration₄ b a.castSucc := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = ⟨a.succ, by omega⟩ -- check whether the face is the (a + 1)-th
  · subst h
    refine le_sup_of_le_right (le_iSup_of_le ⟨a, Nat.lt_add_one a⟩ ?_)
    exact faceImage_succ_le ⟨a, by omega⟩ b ((Fin.mk_lt_of_lt_val a.2))
  ·
    apply le_sup_of_le_left
    apply le_sup_of_le_left
    by_cases h' : j = b.succ.castSucc
    · subst h'
      --have := faceImage_b_succ_succ_eq ⟨a, by omega⟩ b (by simp [Fin.le_iff_val_le_val])
      sorry
    · sorry    --((faceImage_le_boundary_prod_top _ _ _ hj h).trans (prod_top_le_unionProd _ _)))

end τ

/-- a subcomplex `A` of `Δ[n] ⊗ Δ[2]` which is contained in `τ a b` is contained in
  `∂Δ[n + 2]` iff `A ≠ τ a b`. -/
lemma subcomplex_le_boundaryImage_iff {a b : Fin (n + 1)} (ha : a ≤ b)
    (A : (Δ[n] ⊗ Δ[2]).Subcomplex) (hA : A ≤ τ a b) :
    A ≤ (τ.boundaryImage a b) ↔ A ≠ (τ a b) :=
  letI := g_mono a b ha
  subcomplex_le_boundary_image_iff (g a b) _ hA

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
