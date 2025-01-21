import TopCatModelCategory.CommSq
import TopCatModelCategory.SSet.Boundary

universe u

open CategoryTheory Simplicial Opposite

namespace SSet

variable {n : ℕ}

lemma subcomplexHorn_eq_iSup (i : Fin (n + 1)) :
    subcomplexHorn.{u} n i =
      ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), standardSimplex.face {j.1}ᶜ := by
  ext m j
  simp [standardSimplex.face, subcomplexHorn]
  change ¬ _ ↔ _
  simp [Set.eq_univ_iff_forall]
  rfl

lemma face_le_subcomplexHorn (i j : Fin (n + 1)) (h : i ≠ j):
    standardSimplex.face.{u} {i}ᶜ ≤ subcomplexHorn n j := by
  rw [subcomplexHorn_eq_iSup]
  exact le_iSup (fun (k : ({j}ᶜ : Set (Fin (n + 1)))) ↦ standardSimplex.face.{u} {k.1}ᶜ) ⟨i, h⟩

lemma subcomplexHorn_le_subcomplexBoundary (i : Fin (n + 1)) :
    subcomplexHorn.{u} n i ≤ subcomplexBoundary n := by
  rw [subcomplexHorn_eq_iSup]
  simp
  intros
  apply face_le_subcomplexBoundary

instance (i : Fin (n + 1)) : HasDimensionLT (subcomplexHorn.{u} n i) n :=
  Subcomplex.hasDimensionLT_of_le
    (subcomplexHorn_le_subcomplexBoundary i) n

lemma subcomplexHorn_obj_eq_top (i : Fin (n + 1)) (m : ℕ) (h : m + 1 < n) :
    (subcomplexHorn.{u} n i).obj (op [m]) = ⊤ := by
  ext x
  obtain ⟨f, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective x
  obtain ⟨j, hij, hj⟩ : ∃ (j : Fin (n + 1)), j ≠ i ∧ j ∉ Set.range f.toOrderHom := by
    by_contra!
    have : Finset.image f.toOrderHom ⊤ ∪ {i} = ⊤ := by
      ext k
      simp
      by_cases k = i <;> aesop
    have := (congr_arg Finset.card this).symm.le.trans (Finset.card_union_le _ _)
    simp only [SimplexCategory.len_mk, Finset.top_eq_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton, add_le_add_iff_right] at this
    have := this.trans Finset.card_image_le
    simp at this
    omega
  simp [subcomplexHorn_eq_iSup]
  exact ⟨j, hij, fun k hk ↦ hj ⟨k, hk⟩⟩

lemma standardSimplex.subcomplex_le_horn_iff
    (A : (Δ[n + 1] : SSet.{u}).Subcomplex) (i : Fin (n + 2)) :
    A ≤ subcomplexHorn (n + 1) i ↔ ¬ (face {i}ᶜ ≤ A) := by
  constructor
  · intro hA h
    replace h := h.trans hA
    rw [face_singleton_compl, Subcomplex.ofSimplex_le_iff,
      mem_subcomplexHorn_iff] at h
    apply h
    change Set.range (Fin.succAboveOrderEmb i).toOrderHom ∪ _ = _
    rw [Fin.range_succAboveOrderEmb]
    exact Set.compl_union_self {i}
  · intro h
    rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d x hx
    by_cases hd : d < n
    · simp [subcomplexHorn_obj_eq_top i d (by omega)]
    · simp only [not_lt] at hd
      obtain ⟨⟨S, hS⟩, rfl⟩ := standardSimplex.nonDegenerateEquiv.symm.surjective x
      dsimp at hS
      simp only [standardSimplex.nonDegenerateEquiv_symm_mem_iff_face_le] at hx ⊢
      obtain hd | rfl := hd.lt_or_eq
      · obtain rfl : S = Finset.univ := by
          rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
          exact le_antisymm (S.card_le_univ.trans (by simp)) (by omega)
        exfalso
        exact h (le_trans (by simp [face_le_face_iff]) hx)
      · replace hS : Sᶜ.card = 1 := by
          have := S.card_compl_add_card
          rw [Fintype.card_fin] at this
          omega
        obtain ⟨j, rfl⟩ : ∃ j, S = {j}ᶜ := by
          obtain ⟨j, hj⟩ | h :=
            Finset.Nonempty.exists_eq_singleton_or_nontrivial (s := Sᶜ) (by
              rw [← Finset.card_pos]
              omega)
          · exact ⟨j, by simp [← hj]⟩
          · rw [← Finset.one_lt_card_iff_nontrivial] at h
            omega
        apply face_le_subcomplexHorn
        rintro rfl
        exact h hx

namespace subcomplexHorn₂₀

lemma sq : Subcomplex.Sq (standardSimplex.face {0}) (standardSimplex.face {0, 1})
    (standardSimplex.face {0, 2}) (subcomplexHorn 2 0) where
  max_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_subcomplexHorn (2 : Fin 3) 0 (by simp)
      · exact face_le_subcomplexHorn (1 : Fin 3) 0 (by simp)
    · rw [subcomplexHorn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  min_eq := by simp [standardSimplex.face_inter_face]

def ι₀₁ : Δ[1] ⟶ subcomplexHorn.{u} 2 0 :=
  Subcomplex.lift (B := subcomplexHorn 2 0)
    (standardSimplex.{u}.map (SimplexCategory.δ 2))
    (le_antisymm (by simp) (by
      rw [← Subcomplex.image_le_iff, Subcomplex.image_top,
        Subcomplex.range_eq_ofSimplex]
      refine le_trans ?_ (face_le_subcomplexHorn.{u} (2 : Fin 3) 0 (by simp))
      rw [standardSimplex.face_singleton_compl]
      rfl))

def ι₀₂ : Δ[1] ⟶ subcomplexHorn.{u} 2 0 :=
  Subcomplex.lift (standardSimplex.{u}.map (SimplexCategory.δ 1))
    (le_antisymm (by simp) (by
      rw [← Subcomplex.image_le_iff, Subcomplex.image_top,
        Subcomplex.range_eq_ofSimplex]
      refine le_trans ?_ (face_le_subcomplexHorn.{u} (1 : Fin 3) 0 (by simp))
      rw [standardSimplex.face_singleton_compl]
      rfl))

@[reassoc (attr := simp)]
lemma ι₀₁_ι : ι₀₁.{u} ≫ (subcomplexHorn.{u} 2 0).ι =
  standardSimplex.{u}.map (SimplexCategory.δ 2) := by simp [ι₀₁]

@[reassoc (attr := simp)]
lemma ι₀₂_ι : ι₀₂.{u} ≫ (subcomplexHorn.{u} 2 0).ι =
  standardSimplex.{u}.map (SimplexCategory.δ 1) := by simp [ι₀₂]

lemma isPushout :
    IsPushout (standardSimplex.{u}.map (SimplexCategory.δ (1 : Fin 2)))
      (standardSimplex.{u}.map (SimplexCategory.δ (1 : Fin 2))) ι₀₁ ι₀₂ := by
  fapply sq.{u}.isPushout.of_iso'
    (standardSimplex.isoOfRepresentableBy
      (standardSimplex.faceRepresentableBy.{u} {0} 0 (Fin.orderIsoSingleton _)))
    (standardSimplex.isoOfRepresentableBy
      (standardSimplex.faceRepresentableBy.{u} {0, 1} 1 (Fin.orderIsoPair _ _ (by simp))))
    (standardSimplex.isoOfRepresentableBy
      (standardSimplex.faceRepresentableBy.{u} {0, 2} 1 (Fin.orderIsoPair _ _ (by simp))))
    (Iso.refl _)
  all_goals
    rw [← cancel_mono (Subpresheaf.ι _)]
    apply (yonedaEquiv _ _).injective
    ext i : 1
    fin_cases i <;> rfl

end subcomplexHorn₂₀

namespace subcomplexHorn₂₁

lemma sq : Subcomplex.Sq (standardSimplex.face {1}) (standardSimplex.face {0, 1})
    (standardSimplex.face {1, 2}) (subcomplexHorn 2 1) where
  max_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_subcomplexHorn (2 : Fin 3) 1 (by simp)
      · exact face_le_subcomplexHorn (0 : Fin 3) 1 (by simp)
    · rw [subcomplexHorn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  min_eq := by simp [standardSimplex.face_inter_face]

def ι₀₁ : Δ[1] ⟶ subcomplexHorn.{u} 2 1 :=
  Subcomplex.lift (B := subcomplexHorn 2 1)
    (standardSimplex.{u}.map (SimplexCategory.δ 2))
    (le_antisymm (by simp) (by
      rw [← Subcomplex.image_le_iff, Subcomplex.image_top,
        Subcomplex.range_eq_ofSimplex]
      refine le_trans ?_ (face_le_subcomplexHorn.{u} (2 : Fin 3) 1 (by simp))
      rw [standardSimplex.face_singleton_compl]
      rfl))

def ι₁₂ : Δ[1] ⟶ subcomplexHorn.{u} 2 1 :=
  Subcomplex.lift (standardSimplex.{u}.map (SimplexCategory.δ 0))
    (le_antisymm (by simp) (by
      rw [← Subcomplex.image_le_iff, Subcomplex.image_top,
        Subcomplex.range_eq_ofSimplex]
      refine le_trans ?_ (face_le_subcomplexHorn.{u} (0 : Fin 3) 1 (by simp))
      rw [standardSimplex.face_singleton_compl]
      rfl))

@[reassoc (attr := simp)]
lemma ι₀₁_ι : ι₀₁.{u} ≫ (subcomplexHorn.{u} 2 1).ι =
  standardSimplex.{u}.map (SimplexCategory.δ 2) := by simp [ι₀₁]

@[reassoc (attr := simp)]
lemma ι₁₂_ι : ι₁₂.{u} ≫ (subcomplexHorn.{u} 2 1).ι =
  standardSimplex.{u}.map (SimplexCategory.δ 0) := by simp [ι₁₂]

lemma isPushout :
    IsPushout (standardSimplex.{u}.map (SimplexCategory.δ (0 : Fin 2)))
      (standardSimplex.{u}.map (SimplexCategory.δ (1 : Fin 2))) ι₀₁ ι₁₂ := by
  fapply sq.{u}.isPushout.of_iso'
    (standardSimplex.isoOfRepresentableBy
      (standardSimplex.faceRepresentableBy.{u} {1} 0 (Fin.orderIsoSingleton _)))
    (standardSimplex.isoOfRepresentableBy
      (standardSimplex.faceRepresentableBy.{u} {0, 1} 1 (Fin.orderIsoPair _ _ (by simp))))
    (standardSimplex.isoOfRepresentableBy
      (standardSimplex.faceRepresentableBy.{u} {1, 2} 1 (Fin.orderIsoPair _ _ (by simp))))
    (Iso.refl _)
  all_goals
    rw [← cancel_mono (Subpresheaf.ι _)]
    apply (yonedaEquiv _ _).injective
    ext i : 1
    fin_cases i <;> rfl

end subcomplexHorn₂₁

end SSet
