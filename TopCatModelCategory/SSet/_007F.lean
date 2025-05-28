import TopCatModelCategory.SSet._007F_filtration
import TopCatModelCategory.SSet._Order

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

open Subcomplex stdSimplex

variable {n} (a b : Fin (n + 1))

namespace σ

/-- for `0 ≤ a ≤ b < n`, the image of `Λ[n + 1, a + 1]` under `fab : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
def innerHornImage (a b : Fin (n + 1)) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (horn (n + 1) a.succ).image (f a b)

/-- for `0 ≤ a ≤ b < n`, the image of `∂Δ[n + 1]` under `fab : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
def boundaryImage : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (boundary (n + 1)).image (f a b)

/-- image of i-th face under some f : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] -/
@[simp]
noncomputable
def faceImage (i : Fin (n + 2)) (f : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (face {i}ᶜ).image f

-- image of Λ[n + 1, a + 1] under (f a b hab) is the union of the image under f of all faces except
-- the (a + 1)-th
lemma innerHornImage_eq_iSup : innerHornImage a b =
    ⨆ (j : ({a.succ}ᶜ : Set (Fin (n + 2)))), faceImage j.1 (f a b) := by
  simp only [innerHornImage, horn_eq_iSup, image_iSup, faceImage]

lemma boundaryImage_eq_iSup : boundaryImage a b =
    ⨆ (j : Fin (n + 2)), faceImage j.1 (f a b) := by
  simp only [boundaryImage, boundary_eq_iSup, image_iSup, faceImage,
    Fin.cast_val_eq_self]

lemma innerHornImage_le_σ : innerHornImage a b ≤ σ a b := by
  rw [innerHornImage_eq_iSup]
  exact iSup_le fun _ ↦ image_le_range _ (f a b)

lemma faceImage_le_σ (j : Fin (n + 2)) :
    faceImage j (f a b) ≤ σ a b := image_le_range _ (f a b)

/-- each face of `σab` except the `a`-th and `(a+1)`-th is contained in (boundary n).unionProd (horn 2 1) -/
lemma faceImage_le_unionProd (j : Fin (n + 2)) (hj : ¬j = a.succ) (hj' : ¬j = a.castSucc) :
    faceImage j (f a b) ≤ (boundary n).unionProd (horn 2 1) := by
  dsimp [unionProd, faceImage]
  apply le_sup_of_le_right
  rw [face_singleton_compl, image_ofSimplex, ofSimplex_le_iff]
  refine ⟨?_, by simp only [Subpresheaf.top_obj, Set.top_eq_univ, Set.mem_univ]⟩
  change ¬Function.Surjective (a.predAbove ∘ j.succAbove)
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

/-- the `0`-th face of `σ0b` is contained in the unionProd -/
lemma faceImage_zero_le_unionProd : faceImage 0 (f 0 b) ≤ (boundary n).unionProd (horn 2 1) := by
  apply le_sup_of_le_left
  rw [faceImage, face_singleton_compl, image_ofSimplex, ofSimplex_le_iff]
  simp
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (f₂' 0 b ∘ Fin.succ) ∪ {1} ≠ Set.univ
  intro h'
  rw [Set.eq_univ_iff_forall] at h'
  have h'' := h' 0
  simp at h''
  obtain ⟨e, he⟩ := h''
  have := he e.succ_ne_zero
  aesop

/-- for `0 ≤ a < b ≤ n` the `(a+1)`-th face of `σ(a+1)b` is the `(a+1)`-th face of `σab`. -/
lemma faceImage_succ_eq (hab : a < b) :
    faceImage a.succ (f ⟨a.succ, by simp; omega⟩ b) =
      faceImage a.succ (f a b) := by
  dsimp [Subcomplex.unionProd, faceImage]
  rw [face_singleton_compl, image_ofSimplex]
  simp
  congr
  apply Prod.ext
  ·
    simp [f, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ]
    simp [CategoryStruct.comp, SimplexCategory.Hom.mk, SimplexCategory.Hom.toOrderHom]
    simp [Fin.succAboveOrderEmb, OrderEmbedding.ofStrictMono, OrderEmbedding.toOrderHom,
      OrderHom.comp, objMk]
    have : (⟨a.succ, by simp; omega⟩ : Fin (n + 1)).predAbove ∘ a.succ.succAbove =
        a.predAbove ∘ a.succ.succAbove := by
      ext e
      simp [Fin.predAbove, Fin.succAbove]
      split
      · next h =>
        simp_all
        split
        next h_1 =>
          simp_all only [Fin.coe_pred, Fin.coe_castSucc]
          split
          next h_2 => omega
          next h_2 =>
            exfalso
            apply h_2
            have H := Fin.natCast_strictMono (n := n + 1) (by omega) h_1
            have : a < a.succ := by
              refine Fin.lt_iff_val_lt_val.mpr ?_
              simp only [Fin.val_succ, Fin.val_natCast]
              rw [Nat.mod_eq_of_lt]
              all_goals omega
            apply lt_trans this
            rw [← Fin.castSucc_lt_castSucc_iff]
            simp at H
            convert H
            simp [h_1]
            ext
            simp_all only [not_lt, Fin.val_succ, Fin.coe_castSucc, Fin.val_natCast]
            rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
            all_goals omega
        next h_1 =>
          simp_all only [not_lt]
          split
          next h_2 =>
            exfalso
            omega
          next h_2 => omega
      · next h =>
        simp_all
        split
        next h_1 =>
          split
          next h_2 => omega
          next h_2 => omega
        next h_1 =>
          simp_all only [Fin.coe_castPred, Fin.val_succ]
          simp_all only [not_lt]
          split
          next h_2 =>
            exfalso
            apply h
            exact Fin.succ_le_succ_iff.mp h_1
          next h_2 => simp_all only [Fin.coe_castPred, Fin.val_succ]
    aesop
  · have : f₂' (⟨a + 1, by omega⟩ : Fin (n + 1)) b ∘ a.succ.succAbove = f₂' a b ∘ a.succ.succAbove := by
      ext e
      simp [f₂, Fin.succAbove]
      split
      · next h =>
        have h' : e.castSucc ≤ (⟨a + 1, by omega⟩ : Fin (n + 2)) := by
          rcases a with ⟨a, ha⟩
          rcases e with ⟨e, he⟩
          simp at h ⊢
          omega
        simp [h', h]
      · next h =>
        have h' : ¬ e.succ ≤ (⟨a + 1, by omega⟩ : Fin (n + 2)) := by
          rcases a with ⟨a, ha⟩
          rcases e with ⟨e, he⟩
          simp at h ⊢
          omega
        simp [h']
        have h'' : ¬e < a := by omega
        simp [h'']
    simp [f, f₂, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ]
    simp [CategoryStruct.comp, SimplexCategory.Hom.mk, SimplexCategory.Hom.toOrderHom]
    simp [Fin.succAboveOrderEmb, OrderEmbedding.ofStrictMono, OrderEmbedding.toOrderHom,
      OrderHom.comp, objMk]
    simp [objEquiv, Equiv.ulift, SimplexCategory.Hom.mk]
    aesop

/-- for 0 ≤ a < b ≤ n, the (a + 1)-th face of σ(a + 1)b is contained in σab -/
lemma faceImage_succ_le_σ (hab : a < b) :
    faceImage a.succ (f ⟨a.succ, by simp; omega⟩ b) ≤ σ a b := by
  rw [faceImage_succ_eq a b hab]
  exact faceImage_le_σ a b a.succ

/-- for 0 ≤ a < b < n, Λ[n + 1, (a + 1) + 1] ≤ X(b,a) = X(b) ⊔ ... ⊔ σ a b -/
lemma innerHornImage_succ_le_filtration₂ (b : Fin n) (a : Fin b) :
    innerHornImage ⟨a.succ, by omega⟩ b.castSucc
      ≤ filtration₂ b a.castSucc := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = (⟨a.succ, by omega⟩ : Fin (n + 2)) -- check the a-th face first
  · by_cases ha : (⟨a.succ, by omega⟩ : Fin (n + 1)) = 0 -- two cases for a = 0 or a > 0
    · refine le_sup_of_le_left (le_sup_of_le_left ?_)
      aesop
    · subst h
      refine le_sup_of_le_right (le_iSup_of_le ⟨a, Nat.lt_add_one a⟩ ?_)
      exact faceImage_succ_le_σ ⟨a, by omega⟩ b.castSucc (Fin.mk_lt_of_lt_val a.2)
  · refine le_sup_of_le_left (le_sup_of_le_left (faceImage_le_unionProd _ _ _ hj h))

lemma innerHornImage_zero_le_filtration₁_zero :
    innerHornImage (0 : Fin (n + 1)) 0 ≤ filtration₁ 0 := by
  rw [filtration₁_zero, innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  by_cases h : j = 0
  · subst h
    apply le_sup_of_le_left
    simp [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff]
    refine ⟨Set.mem_univ _, ?_⟩
    rw [mem_horn_iff]
    simp [f, f₂]
    change ¬insert 1 (Set.range (f₂' 0 0 ∘ Fin.succ)) = Set.univ
    intro h
    rw [Set.eq_univ_iff_forall] at h
    have := h 0
    simp at this
    obtain ⟨y, hy⟩ := this
    have := hy (Fin.succ_ne_zero y)
    aesop
  · exact faceImage_le_unionProd 0 0 j hj h

lemma innerHornImage_zero_le_filtration₁ (b : Fin n) :
    innerHornImage 0 b.castSucc ≤ filtration₁ b.castSucc := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  by_cases h : j = 0
  · subst h
    apply le_sup_of_le_left
    simp [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff, unionProd]
    left
    refine ⟨Set.mem_univ _, ?_⟩
    rw [mem_horn_iff]
    simp [f]
    change ¬insert 1 (Set.range (f₂' 0 b.castSucc ∘ Fin.succ)) = Set.univ
    intro h
    rw [Set.eq_univ_iff_forall] at h
    have := h 0
    simp at this
    obtain ⟨y, hy⟩ := this
    have := hy (Fin.succ_ne_zero y)
    aesop
  · apply le_sup_of_le_left <| faceImage_le_unionProd 0 b.castSucc j hj h

lemma subcomplex_le_boundaryImage_iff {a b} (A : (Δ[n] ⊗ Δ[2]).Subcomplex) (hA : A ≤ σ a b) :
    A ≤ (boundaryImage a b) ↔ A ≠ (σ a b) :=
  subcomplex_le_boundary_image_iff (f a b) _ hA

lemma subcomplex_le_innerHornImage_iff {n} {a b} (A : (Δ[n] ⊗ Δ[2]).Subcomplex) (hA : A ≤ σ a b) :
    A ≤ innerHornImage a b ↔ ¬ faceImage a.succ (f a b) ≤ A :=
  subcomplex_le_horn_image_iff (f a b) A hA a.succ

lemma faceImage_succ_not_le_unionProd₁ (b : Fin n) (a : Fin b) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (f ⟨a.succ, by omega⟩ b.castSucc)
      ≤ Subcomplex.prod ⊤ Λ[2, 1] := by
  dsimp [faceImage]
  simp [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff]
  refine Set.nmem_setOf_iff.2 ?_
  rw [mem_horn_iff]
  simp
  change insert 1 (Set.range (f₂' _ b.castSucc ∘ Fin.succAbove _)) = Set.univ
  ext i
  simp
  fin_cases i
  · simp
    use a.succ
    simp [Fin.succAbove]
    intro a_1
    split
    next h =>
      simp_all only [↓reduceIte, Fin.isValue]
      split
      next h_1 =>
        simp_all only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
        rw [Fin.lt_iff_val_lt_val] at a_1
        dsimp at a_1
        rw [Nat.mod_eq_of_lt] at a_1
        all_goals omega
      next h_1 =>
        simp_all only [not_le, Fin.isValue, Fin.reduceEq]
        rw [Fin.lt_iff_val_lt_val] at a_1
        dsimp at a_1
        rw [Nat.mod_eq_of_lt] at a_1
        all_goals omega
    next h =>
      simp_all only [↓reduceIte, not_lt, Fin.succ_le_succ_iff, Fin.isValue]
      split
      next h_1 =>
        simp_all only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
        rw [Fin.le_iff_val_le_val] at h
        dsimp at h
        rw [Nat.mod_eq_of_lt] at h
        all_goals omega
      next h_1 =>
        simp_all only [not_le, Fin.isValue, Fin.reduceEq]
        rw [Fin.le_iff_val_le_val] at h
        dsimp at h
        rw [Nat.mod_eq_of_lt] at h
        all_goals omega
  · simp
  · simp
    use b.castSucc.succ
    simp [Fin.succAbove]
    split
    · next h =>
      exfalso
      rw [Fin.lt_iff_val_lt_val] at h
      dsimp at h
      rw [Nat.mod_eq_of_lt] at h
      all_goals omega
    · next h =>
      split
      · next h' =>
        exfalso
        rw [Fin.le_iff_val_le_val] at h'
        dsimp at h'
        rw [Nat.mod_eq_of_lt] at h'
        all_goals omega
      · next h' =>
        simp
        refine Fin.castSucc_lt_iff_succ_le.mpr (le_of_eq ?_)
        ext
        refine Eq.symm (Fin.val_cast_of_lt (Nat.add_lt_add_right b.2 1))

lemma faceImage_succ_not_le_unionProd₂ (b : Fin n) (a : Fin b) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (f ⟨a.succ, by omega⟩ b.castSucc)
      ≤ ∂Δ[n].prod ⊤ := by
  dsimp [faceImage]
  simp [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary, f]
  change Function.Surjective (Fin.predAbove _ ∘ Fin.succAboveOrderEmb _)
  simp [Fin.succAboveOrderEmb]
  intro i
  simp [Fin.predAbove, Fin.succAbove]
  use i
  split
  next h =>
    simp
    intro h'
    exfalso
    rw [Fin.lt_iff_val_lt_val] at h h'
    simp_all
    omega
  next h =>
    simp
    intro h'
    exfalso
    apply h
    rw [Fin.lt_iff_val_lt_val]
    rw [Fin.le_iff_val_le_val] at h'
    simp_all
    omega

lemma faceImage_succ_not_le_σij (b : Fin n) (a j : Fin b) (i : Fin j.succ) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (f ⟨a.succ, by omega⟩ b.castSucc)
      ≤ σ ⟨i, by omega⟩ ⟨j, by omega⟩ := by
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
    have h₁' := congr_fun h₁' b.castSucc
    have h₂' := congr_fun h₂' b.castSucc
    dsimp [objEquiv, Equiv.ulift] at h₁' h₂'
    change (SimplexCategory.σ _) (x b.castSucc) = _ at h₁'
    change (if x _ ≤ _ then 0 else if x _ ≤ _ then 1 else 2) = _ at h₂'
    simp only [Fin.val_succ, Fin.isValue] at h₁' h₂'
    simp only [SimplexCategory.len_mk, ConcreteCategory.hom, SimplexCategory.Hom.toOrderHom,
      SimplexCategory.σ, SimplexCategory.mkHom, SimplexCategory.Hom.mk, SimplexCategory,
      OrderHom.coe_mk, Fin.predAbove, Fin.castSucc_mk, SimplexCategory.δ,
      OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, Fin.succ_succAbove_succ,
      Fin.castSucc_lt_succ_iff, Fin.pred_succ, Fin.isValue, Fin.succ_le_castSucc_iff,
      Fin.succ_le_succ_iff] at h₁' h₂'
    have A : ¬ b.castSucc.castSucc < ⟨a.succ.succ, by omega⟩ := by
      rw [Fin.lt_iff_val_lt_val]
      simp
      omega
    dsimp at A
    simp [Fin.succAbove] at h₁' h₂'
    simp [A] at h₁' h₂'
    split at h₁'
    · next h' =>
      rw [Fin.pred_eq_iff_eq_succ] at h₁'
      simp [h'.not_le] at h₂'
      rw [h₁'] at h₂'
      apply h₂'.not_lt
      rcases j with ⟨j, hj⟩
      rcases b with ⟨b, hb⟩
      simp [hj]
      simp_all only [SimplexCategory.len_mk, Nat.reduceAdd, Fin.castSucc_mk, Fin.succ_mk, Fin.mk_lt_mk,
        add_lt_add_iff_right, Fin.is_lt, ↓reduceDIte, Fin.mk_le_mk, add_le_add_iff_right, Fin.isValue,
        lt_self_iff_false]
      simp_all only [Fin.castSucc_mk, Fin.mk_lt_mk, not_lt, Fin.isValue]
      split at h₂'
      next h_1 =>
        split at h₂'
        next h_2 => simp_all only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
        next h_2 =>
          simp_all only [not_le, Fin.is_lt, Fin.isValue]
          exact hj.not_le h_1
      next h_1 =>
        split at h₂'
        next h_2 => simp_all only [not_le, Fin.isValue, Fin.reduceEq]
        next h_2 => simp_all only [not_le, Fin.is_lt, Fin.isValue, Fin.reduceEq]
    · next h' =>
      simp_all only [SimplexCategory.len_mk, Nat.reduceAdd, Fin.isValue, Int.reduceNeg]
      split at h₂'
      next h_1 =>
        split at h₁'
        next h_2 =>
          split at h₂'
          next h_3 => omega
          next h_3 => simp_all only [not_lt, not_le, Fin.isValue, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one]
        next h_2 =>
          split at h₂'
          next h_3 =>
            simp_all only [Fin.castPred_inj, Fin.isValue]
            simp_all only [not_lt]
            apply h_3.not_lt
            rw [Fin.lt_iff_val_lt_val]
            simp
          next h_3 => simp_all only [Fin.castPred_inj, not_le]
      next h_1 =>
        split at h₁'
        next h_2 =>
          split at h₂'
          next h_3 =>
            split at h₂'
            next h_4 => simp_all only [not_lt, not_le]
            next h_4 => simp_all only [not_lt, not_le]
          next h_3 =>
            split at h₂'
            next h_4 => simp_all only [not_lt, not_le]
            next h_4 => simp_all only [not_lt, not_le]
        next h_2 =>
          split at h₂'
          next h_3 =>
            split at h₂'
            next h_4 => simp_all only [not_le]
            next h_4 => simp_all only [not_le]
          next h_3 =>
            split at h₂'
            next h_4 => simp_all only [not_le]
            next h_4 => simp_all only [not_le]
  · next h =>
    have : ⟨a.succ, by omega⟩ = b.castSucc := by aesop
    have h₁' := congr_fun h₁' ⟨a.succ, by omega⟩
    have h₂' := congr_fun h₂' ⟨a.succ, by omega⟩
    dsimp [objEquiv, Equiv.ulift] at h₁' h₂'
    change (SimplexCategory.σ _) (x ⟨a.succ, by omega⟩) = _ at h₁'
    change (if x ⟨a.succ, by omega⟩ ≤ _ then 0 else if x ⟨a.succ, by omega⟩ ≤ _ then 1 else 2) = _ at h₂'
    rw [this] at h₁'
    simp at this
    simp [ConcreteCategory.hom, SimplexCategory.Hom.toOrderHom, SimplexCategory] at h₁' h₂'
    simp [SimplexCategory.σ, SimplexCategory.δ, SimplexCategory.Hom.mk, Fin.predAbove] at h₁'
    split at h₁'
    · next h' =>
      simp [SimplexCategory.σ, SimplexCategory.δ, SimplexCategory.Hom.mk, Fin.predAbove, h'] at h₂'
      simp [Fin.succAbove] at h₂'
      rw [← this] at h'
      simp [h'] at h₂'
      split at h₂'
      all_goals omega
    · next h' =>
      rw [Fin.castPred_eq_iff_eq_castSucc] at h₁'
      rw [h₁'] at h'
      simp [Fin.succAbove] at h'
      omega

lemma faceImage_succ_not_le_σib {n} (b : Fin n) (a : Fin b) (i : Fin a.succ) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (f ⟨a.succ, by omega⟩ b.castSucc)
      ≤ σ ⟨i, by omega⟩ b.castSucc := by
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
  have h₁' := congr_fun h₁' ⟨a.succ, by omega⟩
  have h₂' := congr_fun h₂' ⟨a.succ, by omega⟩
  simp [objEquiv, Equiv.ulift] at h₁' h₂'
  change (SimplexCategory.σ _) (x ⟨a.succ, by omega⟩) = _ at h₁'
  change (if x ⟨a.succ, by omega⟩ ≤ _ then 0 else if x ⟨a.succ, by omega⟩ ≤ b.castSucc.succ then 1 else 2) = _ at h₂'
  simp only [Fin.val_succ, Fin.isValue] at h₁' h₂'

  by_cases h : (⟨i, by omega⟩ : Fin (n + 1)).castSucc < x ⟨a.succ, by omega⟩
  · simp at h
    simp [h, Fin.pred_eq_iff_eq_succ] at h₁'
    simp [h.not_le, SimplexCategory.δ, SimplexCategory.Hom.mk, Fin.succAbove] at h₂'
    split at h₂'
    all_goals omega
  · simp at h
    simp [h.not_lt, ConcreteCategory.hom, SimplexCategory.Hom.toOrderHom, SimplexCategory.σ,
      SimplexCategory.δ, SimplexCategory.Hom.mk, Fin.predAbove, Fin.succAbove] at h₁'
    simp_rw [h₁'] at h
    apply h.not_lt
    rw[Fin.lt_iff_val_lt_val]
    dsimp
    omega

/-- for `0 ≤ a < b < n`,  show `((a + 1) + 1)`-th face is not contained in anything -/
lemma faceImage_succ_not_le_filtration₂ {n} (b : Fin n) (a : Fin b) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (f ⟨a.succ, by omega⟩ b.castSucc)
      ≤ filtration₂ b a.castSucc := by
  simp [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff, filtration₂,
    filtration₁, unionProd]
  refine ⟨⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, fun j i ↦ ?_⟩, fun i ↦ ?_⟩
  · -- not in `Δ[n] ⨯ Λ[2, 1]`
    simpa [Set.mem_univ, Fin.isValue, true_and, face_singleton_compl, ← image_le_iff,
      image_ofSimplex, ofSimplex_le_iff, Set.prod] using faceImage_succ_not_le_unionProd₁ b a
  · -- not in `∂Δ[n] ⨯ Δ[2]`
    simpa [Set.mem_univ, and_true, face_singleton_compl, ← image_le_iff, image_ofSimplex,
      ofSimplex_le_iff, Set.prod] using faceImage_succ_not_le_unionProd₂ b a
  · -- not in any `σij` for `i ≤ j < b`
    simpa [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff]
      using faceImage_succ_not_le_σij b a j i
  · -- not in any `σib` for any `i < a + 1`
    simpa [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff] using
      faceImage_succ_not_le_σib b a i

lemma faceImage_one_not_le_filtration₁ (b : Fin (n + 1)):
  ¬ faceImage 1 (f 0 b.castSucc) ≤ filtration₁ b.castSucc := by
  simp [face_singleton_compl, ← image_le_iff, image_ofSimplex, ofSimplex_le_iff, filtration₂,
    filtration₁, unionProd]
  refine ⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, ?_⟩
  · simp [mem_horn_iff]
    change insert 1 (Set.range (f₂' 0 b.castSucc ∘ (Fin.succ 0).succAbove)) = Set.univ
    ext i
    fin_cases i
    all_goals simp
    · use 0
      simp
    · use b.castSucc.succ
      simp [Fin.succAbove]
      split
      · next h =>
        exfalso
        simp [Fin.lt_iff_val_lt_val] at h
        rw [Nat.mod_eq_of_lt] at h
        all_goals omega
      · next h =>
        split
        · next h' =>
          exfalso
          exact Fin.succ_ne_zero _ h'
        · next h' =>
          simp [Fin.lt_iff_val_lt_val]
          rw [Nat.mod_eq_of_lt]
          all_goals omega
  · simp [boundary, f]
    change Function.Surjective (Fin.predAbove 0 ∘ (Fin.succ 0).succAboveOrderEmb)
    simp [Fin.succAboveOrderEmb]
    intro i
    use i
    simp [Fin.predAbove, Fin.succAbove]
    split
    next h =>
      simp [Fin.lt_iff_val_lt_val, Nat.lt_one_iff] at h
      aesop
    next h =>
      simp
  · intro j i
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
      Fin.succ_le_succ_iff, Fin.succAbove] at h₁' h₂'
    cases b using Fin.cases with
    | zero => exact Nat.not_succ_le_zero j.1 j.2
    | succ b =>
      split at h₁'
      · next h' =>
        simp_all
        split at h₁'
        · next h'' =>
          exfalso
          apply h''.not_le
          rw [Fin.le_iff_val_le_val]
          simp
          rw [Nat.mod_eq_of_lt]
          all_goals omega
        · next h'' =>
          simp_all [Fin.succ_ne_zero]
          simp_all only [not_lt, Fin.isValue]
          rw [Fin.pred_eq_iff_eq_succ] at h₁'
          erw [h₁'] at h₂'
          split at h₂'
          next h =>
            split at h₂'
            next h_1 => simp_all only [Fin.isValue, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one]
            next h_1 => simp_all only [not_le, Fin.isValue, Fin.reduceEq]
          next h =>
            split at h₂'
            next h_1 =>
              split at h₂'
              next h_2 =>
                simp_all only [not_le, Fin.isValue]
                apply h_1.not_lt
                rw [Fin.lt_iff_val_lt_val]
                simp
                rw [Nat.mod_eq_of_lt]
                all_goals omega
              next h_2 => simp_all only [not_le, Fin.isValue, Fin.reduceEq]
            next h_1 =>
              split at h₂'
              next h_2 => simp_all only [not_le, Fin.isValue, Fin.reduceEq]
              next h_2 =>
                simp_all only [not_le, Fin.isValue]
                apply h_2.not_le
                rw [Fin.le_iff_val_le_val]
                simp
                rw [Nat.mod_eq_of_lt]
                omega
      · next h' =>
        rw [not_lt] at h'
        simp at h'
        simp [h'] at h₂'
        split at h₂'
        · next h'' =>
          exfalso
          apply h''.not_le
          rw [Fin.le_iff_val_le_val]
          simp
          rw [Nat.mod_eq_of_lt]
          all_goals omega
        · next h'' =>
          simp_all only [SimplexCategory.len_mk, Fin.val_succ, Nat.reduceAdd, Fin.castSucc_zero, ↓reduceIte,
            Fin.succ_pos, ↓reduceDIte, Fin.pred_succ, not_lt, Fin.isValue, Fin.succ_le_succ_iff]
          split at h₂'
          next h =>
            simp_all only [Fin.isValue, Fin.succ_ne_zero]
          next h =>
            split at h₂'
            next h_1 => simp_all only [Fin.isValue, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one]
            next h_1 => simp_all only [not_le, Fin.isValue, Fin.reduceEq]

end σ

/-
for `0 ≤ a < b < n`, (so for `n ≥ 2`) the following square

`0 ≤ b < n`
`X(b) ↪ X(b) ∪ σ0b`
`filtration₁ b ↪ filtration₂ b 0`

need
`Λ[n+1,1]` ---> `X(0)`
    |             |
    |             |
    v             V
  `σ00` ---> `X(0) ∪ σ00 = X(1)`
and
`Λ[n+1,1]` ---> `X(1)`
    |             |
    |             |
    v             V
  `σ01` ---> `X(1) ∪ σ01`

first is `0 = a, 1 = b`
`Λ[n+1,2]` --> `X(1) ∪ σ01 = X(0) ∪ σ00 ∪ σ01`
    |                   |
    |                   |
    v                   V
`σ11` --------> `X(1) ∪ σ01 ∪ σ11`

last is `n-2 = a, n-1 = b.`
`Λ[n+1,n]` -------> `X(n-1, n-2)`
     |                    |
     |                    |
     v                    V
`σ(n-1)(n-1)` ---> `X(n-1, n-1) = X(n)`

`Λ[n+1,(a+1)+1]` -------> `X(b) ∪ σ0b ∪ ... ∪ σab`
        |                             |
        |                             |
        v                             V
    `σ(a+1)b` ------> `X(b) ∪ σ0b ∪ ... ∪ σab ∪ σ(a+1)b`

so this says `X(b,a) ↪ X(b,a+1)` is inner anodyne

need `b < n` because `X(n)` is the last term. `X(n-1, n-1) = X(n)`.
need `a < b` because we need `a + 1 ≤ b`
-/

def filtrationPushout_intermediate (n) (b : Fin n) (a : Fin b) :
    Sq
      (σ.innerHornImage ⟨a.succ, by omega⟩ b.castSucc)
      (σ ⟨a.succ, by omega⟩ b.castSucc)
      (filtration₂ b a.castSucc)
      (filtration₂ b a.succ)
      where
  max_eq := by rw [filtration₂_succ b a, sup_comm]
  min_eq := by
    apply le_antisymm
    · rw [σ.subcomplex_le_innerHornImage_iff _ inf_le_left, le_inf_iff, not_and]
      exact fun _ h ↦ (σ.faceImage_succ_not_le_filtration₂ b a) h
    · exact le_inf (σ.innerHornImage_le_σ _ _) (σ.innerHornImage_succ_le_filtration₂ _ _)

/--
`0 ≤ b < (n + 1)`
`X(b) ↪ X(b, 0)`
`filtration₁ b ↪ filtration₂ b 0`

so this says `X(b-1,b-1) = X(b) ↪ X(b,0)` is inner anodyne
-/
def filtrationPushout_join (n) (b : Fin (n + 1)) :
    Sq
      (σ.innerHornImage 0 b.castSucc)
      (σ 0 b.castSucc)
      (filtration₁ b.castSucc)
      (filtration₂ b ⟨0, Nat.zero_lt_succ _⟩)
      where
  max_eq := by
    cases b using Fin.cases with
    | zero => simp [filtration₁, filtration₂, sup_comm]
    | succ => rw [filtration₂_zero, ← Fin.succ_castSucc, filtration₁_succ, sup_comm]
  min_eq := by
    apply le_antisymm
    · rw [σ.subcomplex_le_innerHornImage_iff _ inf_le_left, le_inf_iff, not_and]
      exact fun _ h ↦ σ.faceImage_one_not_le_filtration₁ b h
    · apply le_inf (σ.innerHornImage_le_σ 0 _) (σ.innerHornImage_zero_le_filtration₁ b)

/-
`Λ[n+2,1]` ---> `X(0)`
    |             |
    |             |
    v             V
  `σ00` ------> `X(1)`
-/
def filtrationPushout_zero (n) :
    Sq
      (σ.innerHornImage 0 0)
      (σ 0 0)
      (filtration₁ 0)
      (filtration₁ (1 : Fin (n + 2))) := by
  have h := filtration₁_succ (0 : Fin (n + 1))
  have h' := filtration₂_zero (0 : Fin (n + 1))
  dsimp at h h'
  rw [h]
  simp
  rw [← h']
  exact filtrationPushout_join n 0

variable (b : Fin n) (a : Fin b.1)

#check Subcomplex.isColimitPushoutCoconeOfPullback (f (n := n) a.succ b)
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


/-
have for `0 ≤ b < n`, `X(b) ↪ X(b, 0)`
have for `0 ≤ a < b < n`, `X(b, a) ↪ X(b, a + 1)`

so we have `X(0) ≤ X(0, 0) = X(1) ≤ X(1, 0) ≤ X(1, 1) = X(2) ≤ ...`
  `... ≤ X(n-1) ≤ X(n-1, 0) ≤ X(n-1, n-2) ≤ X(n-1, n-1) = X(n)`

`X(0, 0) ≤ X(1, 0) ≤ X(1, 1) ≤ X(2, 0) ≤ ... ≤ X(n-2, n-2) ≤ X(n-1, 0) ≤ X(n-1, n-2) ≤ X(n-1, n-1)`

-/
