import TopCatModelCategory.CommSq
import TopCatModelCategory.SSet.Boundary

universe u

open CategoryTheory Category Limits Simplicial Opposite

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

namespace subcomplexHorn

def faceι (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    (standardSimplex.face {j}ᶜ : SSet.{u}) ⟶ (subcomplexHorn (n + 1) i : SSet.{u}) :=
  Subcomplex.homOfLE (face_le_subcomplexHorn j i hij)

@[reassoc (attr := simp)]
lemma faceι_ι (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    faceι i j hij ≫ (subcomplexHorn.{u} (n + 1) i).ι = (standardSimplex.face {j}ᶜ).ι := by
  simp [faceι]

def ι (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    Δ[n] ⟶ subcomplexHorn.{u} (n + 1) i :=
  Subcomplex.lift ((standardSimplex.{u}.map (SimplexCategory.δ j)))
    (le_antisymm (by simp) (by
      rw [← Subcomplex.image_le_iff, Subcomplex.image_top,
        Subcomplex.range_eq_ofSimplex]
      refine le_trans ?_ (face_le_subcomplexHorn j i hij)
      rw [standardSimplex.face_singleton_compl]
      rfl))

@[reassoc (attr := simp)]
lemma ι_ι (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    ι i j hij ≫ (subcomplexHorn.{u} (n + 1) i).ι =
      standardSimplex.{u}.map (SimplexCategory.δ j) := by simp [ι]

@[reassoc (attr := simp)]
lemma faceSingletonComplIso_inv_ι (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    (standardSimplex.faceSingletonComplIso j).inv ≫ ι i j hij = faceι i j hij := by
  rw [← cancel_epi (standardSimplex.faceSingletonComplIso j).hom, Iso.hom_inv_id_assoc]
  rfl

end subcomplexHorn

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

abbrev ι₀₁ : Δ[1] ⟶ subcomplexHorn.{u} 2 0 := subcomplexHorn.ι 0 2 (by simp)

abbrev ι₀₂ : Δ[1] ⟶ subcomplexHorn.{u} 2 0 := subcomplexHorn.ι 0 1 (by simp)

lemma isPushout :
    IsPushout (standardSimplex.{u}.map (SimplexCategory.δ (1 : Fin 2)))
      (standardSimplex.{u}.map (SimplexCategory.δ (1 : Fin 2))) ι₀₁ ι₀₂ := by
  fapply sq.{u}.isPushout.of_iso'
    (standardSimplex.faceSingletonIso _ )
    (standardSimplex.facePairIso _ _ (by simp))
    (standardSimplex.facePairIso _ _ (by simp))
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

abbrev ι₀₁ : Δ[1] ⟶ subcomplexHorn.{u} 2 1 := subcomplexHorn.ι 1 2 (by simp)

abbrev ι₁₂ : Δ[1] ⟶ subcomplexHorn.{u} 2 1 := subcomplexHorn.ι 1 0 (by simp)

lemma isPushout :
    IsPushout (standardSimplex.{u}.map (SimplexCategory.δ (0 : Fin 2)))
      (standardSimplex.{u}.map (SimplexCategory.δ (1 : Fin 2))) ι₀₁ ι₁₂ := by
  fapply sq.{u}.isPushout.of_iso'
    (standardSimplex.faceSingletonIso _ )
    (standardSimplex.facePairIso _ _ (by simp))
    (standardSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals
    rw [← cancel_mono (Subpresheaf.ι _)]
    apply (yonedaEquiv _ _).injective
    ext i : 1
    fin_cases i <;> rfl

end subcomplexHorn₂₁

namespace subcomplexHorn₂₂

lemma sq : Subcomplex.Sq (standardSimplex.face {2}) (standardSimplex.face {0, 2})
    (standardSimplex.face {1, 2}) (subcomplexHorn 2 2) where
  max_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_subcomplexHorn (1 : Fin 3) 2 (by simp)
      · exact face_le_subcomplexHorn (0 : Fin 3) 2 (by simp)
    · rw [subcomplexHorn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  min_eq := by simp [standardSimplex.face_inter_face]

abbrev ι₀₂ : Δ[1] ⟶ subcomplexHorn.{u} 2 2 := subcomplexHorn.ι 2 1 (by simp)

abbrev ι₁₂ : Δ[1] ⟶ subcomplexHorn.{u} 2 2 := subcomplexHorn.ι 2 0 (by simp)

lemma isPushout :
    IsPushout (standardSimplex.{u}.map (SimplexCategory.δ (0 : Fin 2)))
      (standardSimplex.{u}.map (SimplexCategory.δ (0 : Fin 2))) ι₀₂ ι₁₂ := by
  fapply sq.{u}.isPushout.of_iso'
    (standardSimplex.faceSingletonIso _ )
    (standardSimplex.facePairIso _ _ (by simp))
    (standardSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals
    rw [← cancel_mono (Subpresheaf.ι _)]
    apply (yonedaEquiv _ _).injective
    ext i : 1
    fin_cases i <;> rfl

end subcomplexHorn₂₂

namespace subcomplexHorn

variable (i : Fin (n + 1))

lemma multicoequalizerDiagram :
  CompleteLattice.MulticoequalizerDiagram (subcomplexHorn n i)
    (ι := ({i}ᶜ : Set (Fin (n +1)))) (fun j ↦ standardSimplex.face {j.1}ᶜ)
    (fun j k ↦ standardSimplex.face {j.1, k.1}ᶜ) where
  hX := subcomplexHorn_eq_iSup i
  hV j k := by
    rw [standardSimplex.face_inter_face]
    congr
    aesop

noncomputable def isColimit :
    IsColimit ((multicoequalizerDiagram i).multicofork'.map Subcomplex.toPresheafFunctor) :=
  Subcomplex.multicoforkIsColimit' (multicoequalizerDiagram i)

end subcomplexHorn

namespace subcomplexHorn₃₁

abbrev ι₀ : Δ[2] ⟶ subcomplexHorn.{u} 3 1 := subcomplexHorn.ι 1 0 (by simp)
abbrev ι₂ : Δ[2] ⟶ subcomplexHorn.{u} 3 1 := subcomplexHorn.ι 1 2 (by simp)
abbrev ι₃ : Δ[2] ⟶ subcomplexHorn.{u} 3 1 := subcomplexHorn.ι 1 3 (by simp)

variable {X : SSet.{u}} (f₀ f₂ f₃ : Δ[2] ⟶ X)
  (h₁₂ : standardSimplex.map (SimplexCategory.δ 2) ≫ f₀ =
    standardSimplex.map (SimplexCategory.δ 0) ≫ f₃)
  (h₁₃ : standardSimplex.map (SimplexCategory.δ 1) ≫ f₀ =
    standardSimplex.map (SimplexCategory.δ 0) ≫ f₂)
  (h₂₃ : standardSimplex.map (SimplexCategory.δ 2) ≫ f₂ =
    standardSimplex.map (SimplexCategory.δ 2) ≫ f₃)

namespace desc

@[simps!]
def multicofork :
    Multicofork ((subcomplexHorn.multicoequalizerDiagram (1 : Fin 4)).multispanIndex'.map
      Subcomplex.toPresheafFunctor) :=
  Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ ↦ match i with
    | 0 => (standardSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => by simp at hi
    | 2 => (standardSimplex.faceSingletonComplIso 2).inv ≫ f₂
    | 3 => (standardSimplex.faceSingletonComplIso 3).inv ≫ f₃) (by
      dsimp
      intro x
      fin_cases x
      · dsimp
        simp only [← cancel_epi (standardSimplex.facePairIso.{u} (n := 3) 1 3 (by simp)).hom,
          ← assoc]
        convert h₁₃
        all_goals apply (yonedaEquiv _ _).injective; ext i; fin_cases i <;> rfl
      · dsimp
        simp only [← cancel_epi (standardSimplex.facePairIso.{u} (n := 3) 1 2 (by simp)).hom,
          ← assoc]
        convert h₁₂
        all_goals apply (yonedaEquiv _ _).injective; ext i; fin_cases i <;> rfl
      · dsimp
        simp only [← cancel_epi (standardSimplex.facePairIso.{u} (n := 3) 0 1 (by simp)).hom,
          ← assoc]
        convert h₂₃
        all_goals apply (yonedaEquiv _ _).injective; ext i; fin_cases i <;> rfl)

end desc

noncomputable def desc : (subcomplexHorn 3 1 : SSet.{u}) ⟶ X :=
  (subcomplexHorn.isColimit (n := 3) 1).desc (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃)

@[reassoc (attr := simp)]
lemma ι₀_desc : ι₀ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₀ := by
  rw [← cancel_epi (standardSimplex.faceSingletonComplIso 0).inv, ← assoc,
    subcomplexHorn.faceSingletonComplIso_inv_ι]
  exact (subcomplexHorn.isColimit 1).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₂_desc : ι₂ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₂ := by
  rw [← cancel_epi (standardSimplex.faceSingletonComplIso 2).inv, ← assoc,
    subcomplexHorn.faceSingletonComplIso_inv_ι]
  exact (subcomplexHorn.isColimit 1).fac _ (.right ⟨2, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₃_desc : ι₃ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₃ := by
  rw [← cancel_epi (standardSimplex.faceSingletonComplIso 3).inv, ← assoc,
    subcomplexHorn.faceSingletonComplIso_inv_ι]
  exact (subcomplexHorn.isColimit 1).fac _ (.right ⟨3, by simp⟩)

end subcomplexHorn₃₁

end SSet
