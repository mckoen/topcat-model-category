import TopCatModelCategory.SSet.Subcomplex
import TopCatModelCategory.SSet.StandardSimplex
import TopCatModelCategory.SSet.HasDimensionLT
import TopCatModelCategory.SSet.Monoidal

universe u

open CategoryTheory Simplicial Opposite MonoidalCategory Limits

namespace SSet

variable {n : ℕ}

/-lemma boundary_eq_iSup :
    boundary.{u} n = ⨆ (i : Fin (n + 1)), stdSimplex.face {i}ᶜ := by
  ext
  simp [stdSimplex.face, boundary, Function.Surjective]
  tauto-/

lemma face_le_boundary (i : Fin (n + 1)) :
    stdSimplex.face.{u} {i}ᶜ ≤ boundary n := by
  rw [boundary_eq_iSup]
  exact le_iSup (fun (i : Fin (n +1)) ↦ stdSimplex.face {i}ᶜ) i

lemma non_mem_boundary (n : ℕ) :
    stdSimplex.objMk .id ∉ (boundary.{u} n).obj (op ⦋n⦌) := by
  simp [boundary_eq_iSup]
  intro i hi
  simpa using @hi i (by aesop)

lemma boundary_lt_top (n : ℕ) :
    boundary.{u} n < ⊤ :=
  lt_of_le_not_le (by simp) (fun h ↦ non_mem_boundary n (h _ (by simp)))

lemma boundary_obj_eq_top (m n : ℕ) (h : m < n) :
    (boundary.{u} n).obj (op ⦋m⦌) = ⊤ := by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  obtain _ | n := n
  · simp at h
  · obtain ⟨i, q, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f (fun hf ↦ by
      rw [← SimplexCategory.epi_iff_surjective] at hf
      have := SimplexCategory.le_of_epi (f := f) inferInstance
      omega)
    apply face_le_boundary i
    simp
    intro i
    apply Fin.succAbove_ne

namespace stdSimplex

variable {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)

lemma subcomplex_hasDimensionLT_of_neq_top (h : A ≠ ⊤) :
    HasDimensionLT A n where
  degenerate_eq_top i hi := by
    ext ⟨a, ha⟩
    rw [A.mem_degenerate_iff]
    simp
    obtain hi | rfl := hi.lt_or_eq
    · simp [Δ[n].degenerate_eq_top_of_hasDimensionLT (n + 1) i (by omega)]
    · rw [mem_degenerate_iff_not_mem_nonDegenerate, nonDegenerate_top_dim]
      change a ∉ {objMk .id}
      rintro rfl
      apply h
      ext ⟨m⟩ x
      obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
      simpa using A.map f.op ha

lemma subcomplex_le_boundary_iff :
    A ≤ boundary n ↔ A ≠ ⊤ := by
  constructor
  · rintro h rfl
    exact non_mem_boundary.{u} n (h _ (by simp))
  · intro h
    have := subcomplex_hasDimensionLT_of_neq_top _ h
    rw [Subcomplex.le_iff_contains_nonDegenerate]
    rintro m ⟨x, h₁⟩ h₂
    dsimp at h₂ ⊢
    by_cases h₃ : m < n
    · simp [boundary_obj_eq_top m n (by simpa using h₃)]
    · simp only [not_lt] at h₃
      replace h₁ := (A.mem_nonDegenerate_iff ⟨x, h₂⟩).2 h₁
      rw [nondegenerate_eq_bot_of_hasDimensionLT _ _ _ h₃] at h₁
      simp at h₁

lemma eq_boundary_iff :
    A = boundary n ↔ boundary n ≤ A ∧ A ≠ ⊤ := by
  constructor
  · rintro rfl
    exact ⟨by rfl, (boundary_lt_top n).ne⟩
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm (by rwa [subcomplex_le_boundary_iff]) h₁

instance : HasDimensionLT (boundary.{u} n) n := by
  apply subcomplex_hasDimensionLT_of_neq_top
  intro h
  simpa [h] using non_mem_boundary.{u} n

end stdSimplex

namespace boundary

def faceι (i : Fin (n + 1)) :
    (stdSimplex.face {i}ᶜ : SSet.{u}) ⟶ (boundary n : SSet.{u}) :=
  Subcomplex.homOfLE (face_le_boundary i)

@[reassoc (attr := simp)]
lemma faceι_ι (i : Fin (n + 2)) :
    faceι i ≫ (boundary.{u} (n + 1)).ι = (stdSimplex.face {i}ᶜ).ι := by
  simp [faceι]

def ι (i : Fin (n + 2)) :
    Δ[n] ⟶ boundary.{u} (n + 1) :=
  Subcomplex.lift ((stdSimplex.{u}.map (SimplexCategory.δ i)))
    (le_antisymm (by simp) (by
      rw [← Subcomplex.image_le_iff, Subcomplex.image_top]
      simp only [Subcomplex.range_eq_ofSimplex]
      refine le_trans ?_ (face_le_boundary i)
      rw [stdSimplex.face_singleton_compl]
      rfl))

@[reassoc (attr := simp)]
lemma ι_ι (i : Fin (n + 2)) :
    ι.{u} i ≫ (boundary.{u} (n + 1)).ι =
      stdSimplex.{u}.map (SimplexCategory.δ i) := rfl

@[reassoc (attr := simp)]
lemma faceSingletonComplIso_inv_ι (i : Fin (n + 2)) :
    (stdSimplex.faceSingletonComplIso i).inv ≫ ι i = boundary.faceι i := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso i).hom, Iso.hom_inv_id_assoc]
  rfl

@[ext]
lemma hom_ext {n : ℕ} {X : SSet.{u}} {f g : (boundary (n + 1) : SSet) ⟶ X}
    (h : ∀ (i : Fin (n + 2)), ι i ≫ f = ι i ≫ g) :
    f = g := by
  ext m ⟨x, hx⟩
  simp [boundary_eq_iSup, stdSimplex.face_singleton_compl,
    Subcomplex.mem_ofSimplex_obj_iff] at hx
  obtain ⟨i, ⟨y, rfl⟩⟩ := hx
  exact congr_fun ((congr_app (h i)) _) _

open MonoidalClosed

@[ext]
lemma hom_ext_tensorLeft {n : ℕ} {X Y : SSet.{u}}
    {f g : Y ⊗ (boundary (n + 1) : SSet) ⟶ X}
    (h : ∀ (i : Fin (n + 2)), Y ◁ ι i ≫ f = Y ◁ ι i ≫ g) :
    f = g := by
  apply curry_injective
  apply hom_ext
  intro i
  simp only [← curry_natural_left, h]

@[ext]
lemma hom_ext_tensorRight {n : ℕ} {X Y : SSet.{u}}
    {f g : (boundary (n + 1) : SSet) ⊗ Y ⟶ X}
    (h : ∀ (i : Fin (n + 2)), ι i ▷ Y ≫ f = ι i ▷ Y ≫ g) :
    f = g := by
  rw [← cancel_epi (β_ _ _).hom]
  apply hom_ext_tensorLeft
  intro i
  simp only [BraidedCategory.braiding_naturality_right_assoc, h]

instance {X : Type u} (p : X → Prop) : Mono (show Subtype p ⟶ X from Subtype.val) := by
  simpa only [mono_iff_injective] using Subtype.val_injective

lemma exists_isPushout_of_ne_top {X : SSet.{u}} (A : X.Subcomplex) (hA : A ≠ ⊤) :
    ∃ (B : X.Subcomplex) (lt : A < B) (n : ℕ)
    (t : (boundary n : SSet) ⟶ (A : SSet)) (b : Δ[n] ⟶ B),
    IsPushout t (boundary n).ι (Subcomplex.homOfLE lt.le) b := by
  by_contra h
  apply hA
  ext ⟨n⟩ : 2
  simp only [Subpresheaf.top_obj, Set.top_eq_univ, Set.eq_univ_iff_forall]
  induction' n using SimplexCategory.rec with n
  induction' n using Nat.strong_induction_on with n hn
  by_contra!
  obtain ⟨x, hx⟩ := this
  have hx' : x ∈ X.nonDegenerate _ := fun hx' ↦ by
    rw [mem_degenerate_iff] at hx'
    obtain ⟨m, hm, f, _, y, rfl⟩ := hx'
    exact hx (A.map _ (hn _ hm _))
  apply h
  let A' := A ⊔ .ofSimplex x
  have hA' : x ∈ A'.obj _ := Or.inr (Subcomplex.mem_ofSimplex_obj x)
  have lt : A < A' := lt_of_le_not_le le_sup_left (fun hA ↦ hx (hA _ hA'))
  have hA'' : A.preimage (yonedaEquiv.symm x) = boundary n := by
    rw [stdSimplex.eq_boundary_iff]
    constructor
    · rw [Subcomplex.le_iff_contains_nonDegenerate]
      intro d ⟨y, hy⟩ hy'
      exact hn _ (dim_lt_of_nondegenerate (X := boundary.{u} n) ⟨⟨y, hy'⟩,
        (Subcomplex.mem_nonDegenerate_iff _ ⟨y, hy'⟩).2 hy⟩ _) _
    · intro h
      apply hx
      simpa using h.symm.le _ (by simp : yonedaEquiv (𝟙 _) ∈ _)
  refine ⟨A', lt, n,
    Subcomplex.lift ((boundary _).ι ≫ yonedaEquiv.symm x) (by
      rw [Subcomplex.preimage_eq_top_iff,
        Subcomplex.range_le_iff_nonDegenerate]
      intro d y
      exact hn _ (dim_lt_of_nondegenerate _ y _) _),
    yonedaEquiv.symm ⟨x, hA'⟩,
    ⟨⟨rfl⟩, ⟨evaluationJointlyReflectsColimits _ (fun ⟨m⟩ ↦
      (PushoutCocone.isColimitMapCoconeEquiv _ _).2 ?_)⟩⟩⟩
  apply IsPushout.isColimit
  dsimp
  refine Types.isPushout_of_isPullback_of_mono (X₅ := X.obj _) (k := Subtype.val)
    (r' := Subtype.val) (b' := (yonedaEquiv.symm x).app _) ?_ rfl rfl
      (le_antisymm (by simp) ?_) ?_
  · exact Types.isPullback_of_eq_setPreimage (f := (yonedaEquiv.symm x).app _) _
      (by simp [← hA''])
  · rintro ⟨y, hy⟩ _
    simp only [Subpresheaf.max_obj, Set.mem_union, A'] at hy
    simp only [Subpresheaf.max_obj, Set.sup_eq_union, Set.mem_union,
      Set.mem_range, Subtype.exists, A']
    obtain hy | ⟨z, hz⟩ := hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨stdSimplex.objEquiv.symm z.unop, by rwa [Subtype.ext_iff]⟩
  · induction' m using SimplexCategory.rec with m
    intro x₃ y₃ hx₃ hy₃ h
    simp only [Set.mem_range, Subpresheaf.ι_app, Subtype.exists,
      exists_prop, exists_eq_right] at hx₃ hy₃
    obtain ⟨φ, rfl⟩ := stdSimplex.objEquiv.symm.surjective x₃
    obtain ⟨ψ, rfl⟩ := stdSimplex.objEquiv.symm.surjective y₃
    dsimp at φ ψ
    have : Epi φ := by
      rw [SimplexCategory.epi_iff_surjective]
      exact not_not.1 hx₃
    have : Epi ψ := by
      rw [SimplexCategory.epi_iff_surjective]
      exact not_not.1 hy₃
    obtain rfl := X.unique_nonDegenerate₃ _ φ ⟨x, hx'⟩ rfl ψ ⟨x, hx'⟩ h
    rfl

end boundary

end SSet
