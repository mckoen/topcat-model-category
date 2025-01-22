import TopCatModelCategory.SSet.HasDimensionLT
import TopCatModelCategory.SSet.StrictSegal
import TopCatModelCategory.SSet.Degenerate
import TopCatModelCategory.SSet.SimplexCategory

universe u

open CategoryTheory Opposite Simplicial

theorem Finset.image_comp (f : β → γ) (g : α → β) [DecidableEq β] [DecidableEq γ]
    (a : Finset α) :
    Finset.image (f ∘ g) a = Finset.image f (Finset.image g a) := by aesop

namespace SSet

namespace standardSimplex

instance (n : ℕ) {m : SimplexCategoryᵒᵖ} : Finite ((Δ[n] : SSet.{u}).obj m) := by
  dsimp [standardSimplex, uliftFunctor]
  infer_instance

instance (n i : ℕ) : DFunLike (Δ[n] _[i]) (Fin (i + 1)) (fun _ ↦ Fin (n + 1)) where
  coe x j := (objEquiv _ _ x).toOrderHom j
  coe_injective' j₁ j₂ h := by
    apply (objEquiv _ _).injective
    ext k : 3
    exact congr_fun h k

lemma monotone_apply {n i : ℕ} (x : Δ[n] _[i]) : Monotone (fun (j : Fin (i + 1)) ↦ x j) :=
  (objEquiv _ _ x).toOrderHom.monotone

@[ext]
lemma ext {n : ℕ} (x y : Δ[n] _[i]) (h : ∀ (i : Fin (i + 1)), x i = y i) : x = y := by
  apply (objEquiv _ _).injective
  ext i : 3
  apply h

@[simp]
lemma objEquiv_symm_apply {n m : ℕ} (f : SimplexCategory.mk m ⟶ [n])
    (i : Fin (m + 1)) :
    (objEquiv.{u} _ (op [m])).symm f i = f.toOrderHom i := rfl

@[simps]
def obj₀Equiv {n : ℕ} : Δ[n] _[0] ≃ Fin (n + 1) where
  toFun x := x 0
  invFun i := const _ i _
  left_inv x := by ext i : 1; fin_cases i; rfl
  right_inv _ := rfl

@[simp]
lemma map_objMk {n : SimplexCategory} {m m' : SimplexCategoryᵒᵖ}
    (f : Fin (m.unop.len + 1) →o Fin (n.len + 1)) (g : m ⟶ m') :
    (standardSimplex.{u}.obj n).map g (objMk f) =
      objMk (f.comp g.unop.toOrderHom) := rfl

@[simp]
lemma objMk_apply {n m : ℕ}
    (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    objMk.{u} (n := .mk n) (m := op (.mk m)) f i = f i :=
  rfl

instance (n : SimplexCategory) : (standardSimplex.{u}.obj n).StrictSegal where
  spineToSimplex {j v} := objMk
    { toFun i := obj₀Equiv (v.vertex i)
      monotone' := by
        induction' n using SimplexCategory.rec with n
        rw [Fin.monotone_iff]
        intro i
        rw [← v.arrow_src i, ← v.arrow_tgt i]
        exact (monotone_apply (v.arrow i) (Fin.zero_le (1 : Fin 2))) }
  spine_spineToSimplex {i} p := by
    induction' n using SimplexCategory.rec with n
    dsimp
    ext j k : 3
    · fin_cases k
      rfl
    · fin_cases k
      · exact (DFunLike.congr_fun (p.arrow_src j) 0).symm
      · exact (DFunLike.congr_fun (p.arrow_tgt j) 0).symm
  spineToSimplex_spine x := by
    induction' n using SimplexCategory.rec with n
    ext
    rfl

@[ext]
lemma path_ext {n i : ℕ} {x y : Path Δ[n] i} (h : x.vertex = y.vertex) : x = y := by
  obtain ⟨v, a, h₁, h₂⟩ := x
  obtain ⟨w, b, h₃, h₄⟩ := y
  obtain rfl := h
  dsimp at h₃ h₄
  simp only [Path.mk.injEq, true_and]
  ext j k : 2
  fin_cases k
  · exact (DFunLike.congr_fun (h₁ j) 0).trans (DFunLike.congr_fun (h₃ j) 0).symm
  · exact (DFunLike.congr_fun (h₂ j) 0).trans (DFunLike.congr_fun (h₄ j) 0).symm

lemma mono_iff (n : ℕ) (f : Δ[n] ⟶ Y) :
    Mono f ↔ Function.Injective (f.app (op [0])):= by
  constructor
  · intro hf
    rw [NatTrans.mono_iff_mono_app] at hf
    simp only [mono_iff_injective] at hf
    apply hf
  · intro hf
    rw [mono_iff_of_strictSegal]
    intro x₁ x₂ h
    apply StrictSegal.spineInjective
    ext i : 2
    apply hf
    dsimp [StrictSegal.spineEquiv, spine]
    simp only [FunctorToTypes.naturality, h]

variable {n : ℕ}

@[ext]
lemma ext' {j : SimplexCategoryᵒᵖ} {x y : (Δ[n] : SSet.{u}).obj j} -- duplicate?
    (h : objEquiv _ _ x = objEquiv _ _ y) : x = y :=
  (objEquiv _ _).injective h

attribute [local simp] Finset.image_subset_iff

@[simps (config := .lemmasOnly)]
def face (S : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex where
  obj U := setOf (fun f ↦ Finset.image ((objEquiv _ _) f).toOrderHom ⊤ ≤ S)
  map {U V} i := by
    simp
    intro x hx y
    apply hx

@[simp]
lemma mem_face_iff (S : Finset (Fin (n + 1))) {d : ℕ} (x : (Δ[n] : SSet.{u}) _[d]) :
    x ∈ (face S).obj _ ↔ ∀ (i : Fin (d + 1)), x i ∈ S := by
  simp [face]
  rfl

@[simp]
lemma Subcomplex.inter_obj {X : SSet.{u}} (A B : X.Subcomplex) (n : SimplexCategoryᵒᵖ) :
    (A ⊓ B).obj n = A.obj n ⊓ B.obj n := rfl

lemma face_inter_face (S₁ S₂ : Finset (Fin (n + 1))) :
    face S₁ ⊓ face S₂ = face (S₁ ⊓ S₂) := by
  dsimp [face]
  aesop

def faceRepresentableBy (S : Finset (Fin (n + 1)))
    (m : ℕ) (e : Fin (m + 1) ≃o S) :
    (face S : SSet.{u}).RepresentableBy (.mk m) where
  homEquiv {j} :=
    { toFun f := ⟨objMk ((OrderHom.Subtype.val S.toSet).comp
          (e.toOrderEmbedding.toOrderHom.comp f.toOrderHom)), fun _ ↦ by aesop⟩
      invFun := fun ⟨x, hx⟩ ↦ SimplexCategory.Hom.mk
        { toFun i := e.symm ⟨(objEquiv _ _ x).toOrderHom i, hx (by aesop)⟩
          monotone' i₁ i₂ h := e.symm.monotone (by
            simp only [Subtype.mk_le_mk]
            exact OrderHom.monotone _ h) }
      left_inv f := by
        ext i : 3
        apply e.symm_apply_apply
      right_inv := fun ⟨x, hx⟩ ↦ by
        dsimp
        ext i : 5
        exact congr_arg Subtype.val
          (e.apply_symm_apply ⟨(objEquiv _ _ x).toOrderHom i, _⟩) }
  homEquiv_comp f g := by aesop

def isoOfRepresentableBy {X : SSet.{u}} {m : ℕ} (h : X.RepresentableBy (.mk m)) :
    Δ[m] ≅ X :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso ((objEquiv _ _).trans h.homEquiv)) (by
    intros
    ext x
    apply h.homEquiv_comp)

lemma obj₀Equiv_symm_mem_face_iff (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    (obj₀Equiv.symm i) ∈ (face S).obj (op (.mk 0)) ↔ i ∈ S := by
  constructor
  · intro h
    simp at h
    exact h 0
  · aesop

lemma face_le_face_iff (S₁ S₂ : Finset (Fin (n + 1))) :
    face.{u} S₁ ≤ face S₂ ↔ S₁ ≤ S₂ := by
  constructor
  · intro h i hi
    simp only [← obj₀Equiv_symm_mem_face_iff.{u}] at hi ⊢
    exact h _ hi
  · intro h d a ha
    dsimp [face] at ha ⊢
    exact ha.trans h

lemma face_eq_ofSimplex (S : Finset (Fin (n + 1))) (m : ℕ) (e : Fin (m + 1) ≃o S) :
    face.{u} S = Subcomplex.ofSimplex (n := m)
        (by exact objMk ((OrderHom.Subtype.val S.toSet).comp e.toOrderEmbedding.toOrderHom)) := by
  apply le_antisymm
  · rintro ⟨k⟩ x hx
    induction' k using SimplexCategory.rec with k
    rw [mem_face_iff] at hx
    let φ : Fin (k + 1) →o S :=
      { toFun i := ⟨x i, hx i⟩
        monotone' := (objEquiv _ _ x).toOrderHom.monotone }
    refine ⟨standardSimplex.objMk
      (e.symm.toOrderEmbedding.toOrderHom.comp φ), ?_⟩
    obtain ⟨f, rfl⟩ := (objEquiv _ _).symm.surjective x
    ext j : 1
    simpa only [Subtype.ext_iff] using e.apply_symm_apply ⟨_, hx j⟩
  · simp [Subcomplex.ofSimplex_le_iff]

lemma face_singleton_compl (i : Fin (n + 2)) :
    face.{u} {i}ᶜ =
      Subcomplex.ofSimplex (n := n) (objMk (SimplexCategory.δ i).toOrderHom) := by
  let e : Fin (n + 1) ≃o ({i}ᶜ : Finset _) :=
    { toEquiv := (finSuccAboveEquiv (p := i)).trans
        { toFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩
          invFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩
          left_inv _ := rfl
          right_inv _ := rfl }
      map_rel_iff' := (Fin.succAboveOrderEmb i).map_rel_iff }
  exact face_eq_ofSimplex _ _ e

def faceSingletonComplIso (i : Fin (n + 2)) :
    Δ[n] ≅ (face {i}ᶜ : SSet.{u}) := by
  apply isoOfRepresentableBy
  apply faceRepresentableBy
  exact
    { toEquiv := (finSuccAboveEquiv (p := i)).trans
        { toFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩
          invFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩
          left_inv _ := rfl
          right_inv _ := rfl }
      map_rel_iff' := (Fin.succAboveOrderEmb i).map_rel_iff }

noncomputable def faceSingletonIso (i : Fin (n + 1)) :
    Δ[0] ≅ (face {i} : SSet.{u}) :=
  standardSimplex.isoOfRepresentableBy
      (standardSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoSingleton i))

noncomputable def facePairIso (i j : Fin (n + 1)) (hij : i < j) :
    Δ[1] ≅ (face {i, j} : SSet.{u}) :=
  standardSimplex.isoOfRepresentableBy
      (standardSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoPair i j hij))

lemma mem_non_degenerate_iff_mono {d : ℕ} (x : (Δ[n] : SSet.{u}) _[d]) :
    x ∈ Δ[n].NonDegenerate d ↔ Mono (objEquiv _ _ x) := by
  obtain ⟨f, rfl⟩ := (objEquiv _ _).symm.surjective x
  simp only [Equiv.apply_symm_apply]
  constructor
  · obtain _ | d := d
    · infer_instance
    · obtain ⟨f, rfl⟩ : ∃ (g : Fin (d + 2) →o Fin (n + 1)), SimplexCategory.mkHom g = f :=
        ⟨f.toOrderHom, rfl⟩
      contrapose
      intro hf
      simp only [SimplexCategory.mono_iff_injective, Fin.orderHom_injective_iff,
        not_forall, Decidable.not_not] at hf
      obtain ⟨i, hi⟩ := hf
      dsimp at i f
      simp only [SimplexCategory.len_mk, SimplexCategory.mkHom,
        SimplexCategory.Hom.toOrderHom_mk] at hi
      simp only [← mem_degenerate_iff_non_mem_nondegenerate, degenerate_eq_iUnion_range_σ,
        Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_range]
      refine ⟨i, objMk (f.comp (SimplexCategory.δ i.castSucc).toOrderHom), ?_⟩
      ext j : 1
      dsimp [SimplicialObject.σ, SimplexCategory.δ, SimplexCategory.σ]
      rw [objEquiv_symm_apply, SimplexCategory.Hom.toOrderHom_mk]
      by_cases hj : j = i.castSucc
      · simpa [hj] using hi.symm
      · exact congr_arg f (Fin.succAbove_predAbove hj)
  · intro
    rw [mem_nondegenerate_iff_not_mem_degenerate, SSet.mem_degenerate_iff]
    rintro ⟨m, hm, p, _, ⟨g, hg⟩⟩
    obtain ⟨g, rfl⟩ := (objEquiv _ _).symm.surjective g
    simp only [map_apply, Quiver.Hom.unop_op, Equiv.apply_symm_apply,
      EmbeddingLike.apply_eq_iff_eq] at hg
    have := SimplexCategory.le_of_mono (mono_of_mono_fac hg)
    omega

variable (n) in
lemma bijective_image_objEquiv_toOrderHom_top (m : ℕ) :
    Function.Bijective (fun (⟨x, hx⟩ : (Δ[n] : SSet.{u}).NonDegenerate m) ↦
      (⟨Finset.image (objEquiv _ _ x).toOrderHom ⊤, by
        rw [mem_non_degenerate_iff_mono, SimplexCategory.mono_iff_injective] at hx
        dsimp
        rw [Finset.card_image_of_injective _ (by exact hx), Finset.card_univ,
          Fintype.card_fin]⟩ : { S : Finset (Fin (n + 1)) | S.card = m + 1 })) := by
  constructor
  · rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h₃
    obtain ⟨f₁, rfl⟩ := (objEquiv _ _ ).symm.surjective x₁
    obtain ⟨f₂, rfl⟩ := (objEquiv _ _ ).symm.surjective x₂
    simp [mem_non_degenerate_iff_mono, SimplexCategory.mono_iff_injective] at h₁ h₂
    simp at h₃ ⊢
    apply SimplexCategory.Hom.ext
    apply Fin.orderHom_ext_of_injective h₁ h₂ h₃
  · intro ⟨S, hS⟩
    dsimp at hS
    let e := monoEquivOfFin S (k := m + 1) (by simpa using hS)
    refine ⟨⟨objMk ((OrderHom.Subtype.val _).comp (e.toOrderEmbedding.toOrderHom)), ?_⟩, ?_⟩
    · rw [mem_non_degenerate_iff_mono, SimplexCategory.mono_iff_injective]
      intro a b h
      apply e.injective
      ext : 1
      exact h
    · simp [e, Finset.image_comp, Finset.image_univ_of_surjective e.surjective]

noncomputable def nonDegenerateEquiv {m : ℕ} : (Δ[n] : SSet.{u}).NonDegenerate m ≃
    { S : Finset (Fin (n + 1)) | S.card = m + 1 } :=
  Equiv.ofBijective _ (bijective_image_objEquiv_toOrderHom_top n m)

@[simp]
lemma nonDegenerateEquiv_iff {m : ℕ} (x : (Δ[n] : SSet.{u}).NonDegenerate m) (j : Fin (n + 1)):
    j ∈ (nonDegenerateEquiv x).1 ↔ ∃ (i : Fin (m + 1)), x.1 i = j := by
  dsimp [nonDegenerateEquiv]
  aesop

noncomputable def orderIsoOfNonDegenerate {m : ℕ} (x : (Δ[n] : SSet.{u}).NonDegenerate m) :
    Fin (m + 1) ≃o (nonDegenerateEquiv x).1 where
  toEquiv := Equiv.ofBijective (fun i ↦ ⟨x.1 i, Finset.mem_image_of_mem _ (by simp)⟩) (by
    constructor
    · have := (mem_non_degenerate_iff_mono x.1).1 x.2
      rw [SimplexCategory.mono_iff_injective] at this
      exact fun _ _ h ↦ this (by simpa using h)
    · rintro ⟨j, hj⟩
      rw [nonDegenerateEquiv_iff] at hj
      aesop)
  map_rel_iff' := by
    have := (mem_non_degenerate_iff_mono x.1).1 x.2
    rw [SimplexCategory.mono_iff_injective] at this
    intro a b
    dsimp
    simp only [Subtype.mk_le_mk]
    constructor
    · rw [← not_lt, ← not_lt]
      intro h h'
      apply h
      obtain h'' | h'' := (monotone_apply x.1 h'.le).lt_or_eq
      · assumption
      · simp only [this h'', lt_self_iff_false] at h'
    · intro h
      exact monotone_apply _ h

lemma face_nonDegenerateEquiv {m : ℕ} (x : (Δ[n] : SSet.{u}).NonDegenerate m) :
    face (nonDegenerateEquiv x).1 = Subcomplex.ofSimplex x.1 :=
  face_eq_ofSimplex.{u} _ _ (orderIsoOfNonDegenerate x)

lemma nonDegenerateEquiv_symm_apply_mem {m : ℕ}
    (S : { S : Finset (Fin (n + 1)) | S.card = m + 1 }) (i : Fin (m + 1)) :
      (nonDegenerateEquiv.{u}.symm S).1 i ∈ S.1 := by
  obtain ⟨f, rfl⟩ := nonDegenerateEquiv.{u}.surjective S
  dsimp [nonDegenerateEquiv]
  simp only [Equiv.ofBijective_symm_apply_apply, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, rfl⟩

lemma nonDegenerateEquiv_symm_mem_iff_face_le {m : ℕ}
    (S : { S : Finset (Fin (n + 1)) | S.card = m + 1 })
    (A : (Δ[n] : SSet.{u}).Subcomplex) :
    (nonDegenerateEquiv.symm S).1 ∈ A.obj _ ↔ face S ≤ A := by
  obtain ⟨x, rfl⟩ := nonDegenerateEquiv.{u}.surjective S
  rw [face_nonDegenerateEquiv x, Equiv.symm_apply_apply, Subcomplex.ofSimplex_le_iff]

lemma non_degenerate_top_dim :
    (Δ[n] : SSet.{u}).NonDegenerate n = {objMk .id} := by
  ext x
  obtain ⟨f, rfl⟩ := (objEquiv _ _).symm.surjective x
  simp only [Set.mem_singleton_iff, mem_non_degenerate_iff_mono, Equiv.apply_symm_apply]
  trans f = 𝟙 _
  · constructor
    · intro
      exact SimplexCategory.eq_id_of_mono f
    · rintro rfl
      infer_instance
  · exact (Equiv.apply_eq_iff_eq _).symm

instance : (Δ[n] : SSet.{u}).HasDimensionLT (n + 1) where
  degenerate_eq_top i hi := by
    ext x
    obtain ⟨f, rfl⟩ := (objEquiv _ _).symm.surjective x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    rw [mem_degenerate_iff_non_mem_nondegenerate, mem_non_degenerate_iff_mono,
      Equiv.apply_symm_apply]
    intro hf
    have := SimplexCategory.le_of_mono (f := f) inferInstance
    omega

end standardSimplex

end SSet
