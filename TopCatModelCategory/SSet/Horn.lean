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

end SSet
