import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.SSet.DeformationRetract
import TopCatModelCategory.SSet.Degenerate
import TopCatModelCategory.SSet.Fibrations
import TopCatModelCategory.SSet.FundamentalGroupoid
import TopCatModelCategory.Set

universe u

open CategoryTheory HomotopicalAlgebra Simplicial MonoidalCategory
  ChosenFiniteProducts Category Limits

namespace SSet.Subcomplex

@[simps]
def evaluation (X : SSet.{u}) (j : SimplexCategoryᵒᵖ) :
    X.Subcomplex ⥤ Set (X.obj j) where
  obj A := A.obj j
  map f := CategoryTheory.homOfLE (leOfHom f j)

instance {J : Type*} [Category J] {X : SSet.{u}} [IsFilteredOrEmpty J] :
    PreservesColimitsOfShape J (Subcomplex.toPresheafFunctor (X := X)) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone (CompleteLattice.isColimitCocone F)
      (evaluationJointlyReflectsColimits _ (fun j ↦
        IsColimit.ofIsoColimit (isColimitOfPreserves Set.toTypes
          (CompleteLattice.isColimitCocone (F ⋙ evaluation _ j)))
            (Cocones.ext (Set.toTypes.mapIso (eqToIso (by simp))))))

end SSet.Subcomplex

lemma CategoryTheory.IsPullback.types_ext {A B C D : Type u} {t : A ⟶ B} {l : A ⟶ C}
    {r : B ⟶ D} {b : C ⟶ D} (h : IsPullback t l r b) {x y : A}
    (h₁ : t x = t y) (h₂ : l x = l y) : x = y := by
  apply (PullbackCone.IsLimit.equivPullbackObj h.isLimit).injective
  ext <;> assumption

namespace SSet

variable {E B : SSet.{u}} (p : E ⟶ B)

structure SimplexOverRelStruct {n : ℕ} (x y : E _[n]) where
  h : Δ[n] ⊗ Δ[1] ⟶ E
  h₀ : ι₀ ≫ h = (yonedaEquiv _ _).symm x
  h₁ : ι₁ ≫ h = (yonedaEquiv _ _).symm y
  π : Δ[n] ⟶ B
  d : ∂Δ[n] ⟶ E
  hπ : h ≫ p = fst _ _ ≫ π
  hd : (subcomplexBoundary.{u} n).ι ▷ Δ[1] ≫ h = fst _ _ ≫ d

namespace SimplexOverRelStruct

section

variable {p} {n : ℕ} {x y : E _[n]} (rel : SimplexOverRelStruct p x y)

lemma π_eq₁ : rel.π = (yonedaEquiv _ _).symm x ≫ p := by
  rw [← rel.h₀, Category.assoc, rel.hπ, lift_fst_assoc, id_comp]

lemma π_eq₂ : rel.π = (yonedaEquiv _ _).symm y ≫ p := by
  rw [← rel.h₁, Category.assoc, rel.hπ, lift_fst_assoc, id_comp]

lemma d_eq₁ : rel.d = (subcomplexBoundary n).ι ≫ (yonedaEquiv _ _).symm x := by
  rw [← rel.h₀, ← ι₀_comp_assoc, rel.hd]
  rfl

lemma d_eq₂ : rel.d = (subcomplexBoundary n).ι ≫ (yonedaEquiv _ _).symm y := by
  rw [← rel.h₁, ← ι₁_comp_assoc, rel.hd]
  rfl

lemma sq : CommSq rel.d (subcomplexBoundary.{u} n).ι p rel.π := ⟨by simp [π_eq₁, d_eq₁]⟩

end

variable {p} in
@[ext]
lemma ext {n : ℕ} {x y : E _[n]}
    {rel₁ rel₂ : SimplexOverRelStruct p x y} (h : rel₁.h = rel₂.h) :
    rel₁ = rel₂ := by
  suffices rel₁.π = rel₂.π ∧ rel₁.d = rel₂.d by
    cases rel₁
    cases rel₂
    obtain rfl := h
    obtain rfl := this.1
    obtain rfl := this.2
    rfl
  simp [π_eq₁, d_eq₁]

noncomputable def refl (x : E _[n]) : SimplexOverRelStruct p x x where
  h := fst _ _ ≫ (yonedaEquiv _ _).symm x
  h₀ := rfl
  h₁ := rfl
  π := (yonedaEquiv _ _).symm x ≫ p
  d := (subcomplexBoundary.{u} n).ι ≫ (yonedaEquiv _ _).symm x
  hπ := rfl
  hd := rfl

section

variable {p} {n : ℕ} {π : Δ[n] ⟶ B} {d : ∂Δ[n] ⟶ E}
  (sq : CommSq d (subcomplexBoundary.{u} n).ι p π)

noncomputable def ihomToPullbackFiberMk (x : E _[n])
    (hx₁ : (subcomplexBoundary n).ι ≫ (yonedaEquiv _ _).symm x = d)
    (hx₂ : (yonedaEquiv _ _).symm x ≫ p = π) :
    (ihomToPullbackFiber sq : SSet) _[0] :=
  ⟨ihom₀Equiv.symm ((yonedaEquiv _ _).symm x), by
    rw [ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff]
    exact ⟨hx₁, hx₂⟩⟩

open KanComplex.FundamentalGroupoid

namespace equiv

open MonoidalClosed

variable (x y : E _[n])
    {hx₁ : (subcomplexBoundary n).ι ≫ (yonedaEquiv _ _).symm x = d}
    {hx₂ : (yonedaEquiv _ _).symm x ≫ p = π}
    {hy₁ : (subcomplexBoundary n).ι ≫ (yonedaEquiv _ _).symm y = d}
    {hy₂ : (yonedaEquiv _ _).symm y ≫ p = π}

@[simps! map]
noncomputable def toFun (rel : SimplexOverRelStruct p x y) :
      Edge (.mk (ihomToPullbackFiberMk sq x hx₁ hx₂))
        (.mk (ihomToPullbackFiberMk sq y hy₁ hy₂)) :=
  Edge.mk
    ((ihomToPullbackFiber sq).lift (curry rel.h) (by
      rw [Subcomplex.preimage_eq_top_iff,
        range_le_ihomToPullbackFiber_iff]
      constructor
      · rw [← curry_whiskerRight_comp, rel.hd, ← hx₁, rel.d_eq₁]
        rfl
      · rw [← curry_natural_right, rel.hπ, ← hx₂, rel.π_eq₁]
        rfl)) (by
        rw [← cancel_mono (Subpresheaf.ι _), Category.assoc, Subcomplex.lift_ι,
          ← curry_natural_left]
        -- could be better with `curry'`
        apply uncurry_injective
        rw [uncurry_curry, ← cancel_epi (standardSimplex.rightUnitor _).inv]
        exact rel.h₀) (by
        rw [← cancel_mono (Subpresheaf.ι _), Category.assoc, Subcomplex.lift_ι,
          ← curry_natural_left]
        apply uncurry_injective
        rw [uncurry_curry, ← cancel_epi (standardSimplex.rightUnitor _).inv]
        exact rel.h₁)

@[simps]
noncomputable def invFun (e : Edge (.mk (ihomToPullbackFiberMk sq x hx₁ hx₂))
        (.mk (ihomToPullbackFiberMk sq y hy₁ hy₂))) :
    SimplexOverRelStruct p x y where
  h := uncurry (e.map ≫ Subpresheaf.ι _)
  h₀ := by
    rw [← standardSimplex.rightUnitor_inv_map_δ_one, Category.assoc,
      uncurry_natural_left, ← MonoidalCategory.whiskerLeft_comp_assoc, e.comm₀]
    rfl
  h₁ := by
    rw [← standardSimplex.rightUnitor_inv_map_δ_zero, Category.assoc,
      uncurry_natural_left, ← MonoidalCategory.whiskerLeft_comp_assoc, e.comm₁]
    rfl
  π := π
  d := d
  hπ := by
    rw [← MonoidalClosed.uncurry_natural_right, Category.assoc,
      ihomToPullbackFiber_ihom_map]
    rfl
  hd := by
    rw [whiskerRight_comp_uncurry, Category.assoc, ihomToPullbackFiber_pre_app]
    rfl

end equiv

noncomputable def equiv (x y : E _[n])
    (hx₁ : (subcomplexBoundary n).ι ≫ (yonedaEquiv _ _).symm x = d)
    (hx₂ : (yonedaEquiv _ _).symm x ≫ p = π)
    (hy₁ : (subcomplexBoundary n).ι ≫ (yonedaEquiv _ _).symm y = d)
    (hy₂ : (yonedaEquiv _ _).symm y ≫ p = π) :
    SimplexOverRelStruct p x y ≃
      Edge (.mk (ihomToPullbackFiberMk sq x hx₁ hx₂))
        (.mk (ihomToPullbackFiberMk sq y hy₁ hy₂)) where
  toFun := equiv.toFun sq x y
  invFun := equiv.invFun sq x y
  left_inv rel := by aesop
  right_inv e := by aesop

end

variable {p}

noncomputable def symm {x y : E _[n]} [Fibration p] (h : SimplexOverRelStruct p x y) :
    SimplexOverRelStruct p y x :=
  (equiv h.sq y x _ _ _ _).symm
    (equiv h.sq x y h.d_eq₁.symm h.π_eq₁.symm h.d_eq₂.symm h.π_eq₂.symm h).inv

noncomputable def trans {x y z : E _[n]} [Fibration p] (h : SimplexOverRelStruct p x y)
    (h' : SimplexOverRelStruct p y z) :
    SimplexOverRelStruct p x z :=
  (equiv h.sq x z _ _ _ _).symm
    ((equiv h.sq x y h.d_eq₁.symm h.π_eq₁.symm h.d_eq₂.symm h.π_eq₂.symm h).comp
      (equiv h.sq y z h.d_eq₂.symm h.π_eq₂.symm
      (by rw [h.d_eq₂, ← h'.d_eq₁, h'.d_eq₂])
      (by rw [h.π_eq₂, ← h'.π_eq₁, h'.π_eq₂]) h'))

end SimplexOverRelStruct

inductive SimplexOverRel {n : ℕ} : E _[n] → E _[n] → Prop
  | mk {x y : E _[n]} (h : SimplexOverRelStruct p x y) : SimplexOverRel x y

lemma SimplexOverRel.equivalence [Fibration p] (n : ℕ) :
    _root_.Equivalence (SimplexOverRel p (n := n)) where
  refl _ := .mk (.refl _ _)
  symm := fun ⟨h⟩ ↦ .mk h.symm
  trans := fun ⟨h₁⟩ ⟨h₂⟩ ↦ .mk (h₁.trans h₂)

class MinimalFibration extends Fibration p : Prop where
  minimal {n : ℕ} {x y : E _[n]} (rel : SimplexOverRelStruct p x y) : x = y

def minimalFibrations : MorphismProperty (SSet.{u}) :=
  fun _ _ p ↦ MinimalFibration p

lemma minimalFibrations_iff : minimalFibrations p ↔ MinimalFibration p := Iff.rfl

instance : MinimalFibration (𝟙 B) where
  minimal {n x y} rel := by
    apply (yonedaEquiv _ _).symm.injective
    simp only [← rel.h₀, ← rel.h₁, ← cancel_mono (𝟙 B), assoc, rel.hπ,
      lift_fst_assoc, id_comp]

instance : minimalFibrations.{u}.ContainsIdentities where
  id_mem B := by
    rw [minimalFibrations_iff]
    infer_instance

namespace SimplexOverRelStruct

attribute [reassoc] h₀ h₁ hπ hd

variable {p} {n : ℕ} {x y : E _[n]} (rel : SimplexOverRelStruct p x y)

include rel in
@[reassoc]
lemma hπ' : (yonedaEquiv _ _).symm x ≫ p = (yonedaEquiv _ _).symm y ≫ p := by
  simp only [← rel.h₀, ← rel.h₁, assoc, rel.hπ, lift_fst_assoc, id_comp]

include rel in
lemma eq [MinimalFibration p] : x = y := MinimalFibration.minimal rel

include rel in
lemma eq_of_degenerate (hx : x ∈ E.Degenerate n) (hy : y ∈ E.Degenerate n) :
    x = y := by
  obtain _ | n := n
  · simp at hx
  have h₀ := (subcomplexBoundary.{u} (n + 1)).ι ≫= rel.h₀
  have h₁ := (subcomplexBoundary.{u} (n + 1)).ι ≫= rel.h₁
  erw [← ι₀_comp_assoc, rel.hd, ι₀_fst_assoc] at h₀
  erw [← ι₁_comp_assoc, rel.hd, ι₁_fst_assoc] at h₁
  refine eq_of_degenerate_of_δ_eq hx hy (fun i ↦ ?_)
  have := subcomplexBoundary.ι i ≫= (h₀.symm.trans h₁)
  rw [subcomplexBoundary.ι_ι_assoc, subcomplexBoundary.ι_ι_assoc,
    ← yonedaEquiv_symm_map, ← yonedaEquiv_symm_map] at this
  exact (yonedaEquiv _ _).symm.injective this

noncomputable def map
    {E' B' : SSet.{u}} {p' : E' ⟶ B'} (φ : Arrow.mk p ⟶ Arrow.mk p')
    {x' y' : E' _[n]} (hx' : φ.left.app _ x = x') (hy' : φ.left.app _ y = y') :
    SimplexOverRelStruct p' x' y' where
  h := rel.h ≫ φ.left
  h₀ := by rw [rel.h₀_assoc, ← hx', yonedaEquiv_symm_comp]
  h₁ := by rw [rel.h₁_assoc, ← hy', yonedaEquiv_symm_comp]
  π := rel.π ≫ φ.right
  d := rel.d ≫ φ.left
  hπ := by
    have := Arrow.w φ
    dsimp at this
    rw [assoc, this, rel.hπ_assoc]
  hd := by rw [rel.hd_assoc]

end SimplexOverRelStruct

instance : minimalFibrations.{u}.IsStableUnderRetracts where
  of_retract {E B E' B' p p'} h (hp' : MinimalFibration p') := by
    have : Fibration p := by
      have : Fibration p' := inferInstance
      rw [fibration_iff] at this ⊢
      exact (fibrations _).of_retract h this
    constructor
    intro n x y hxy
    have h₁ := congr_arg (h.r.left.app _) ((hxy.map h.i rfl rfl).eq)
    have h₂ (a) : _ = a := congr_fun (NatTrans.congr_app h.left.retract ⟨.mk n⟩) a
    dsimp at h₂
    rw [← h₂ x, h₁, h₂]

-- to be generalized
instance : minimalFibrations.{u}.RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _
    (fun p' p e hp' ↦ (minimalFibrations).of_retract { i := e.inv, r := e.hom } hp')

instance : minimalFibrations.{u}.IsStableUnderBaseChange where
  of_isPullback {E' E B' B b p t p'} h hp' := by
    rw [minimalFibrations_iff] at hp'
    have : Fibration p' := by
      have : Fibration p := by infer_instance
      rw [fibration_iff] at this ⊢
      exact (fibrations SSet.{u}).of_isPullback h this
    constructor
    intro n x y hxy
    apply (h.map ((evaluation _ _).obj _)).types_ext
    · exact (hxy.map (Arrow.homMk t b h.w) rfl rfl).eq
    · apply (yonedaEquiv _ _).symm.injective
      simp [← yonedaEquiv_symm_comp, hxy.hπ']

namespace MinimalFibration

structure Selection where
  set (n : ℕ) : Set (E _[n])
  le_set (n : ℕ) : E.Degenerate n ≤ set n
  unique {n : ℕ} {x y : E _[n]} (hx : x ∈ set n) (hy : y ∈ set n)
    (h : SimplexOverRelStruct p x y) : x = y
  nonempty {n : ℕ} (x : E _[n]) : ∃ (y : E _[n]) (_ : y ∈ set n),
    Nonempty (SimplexOverRelStruct p x y)

-- use that `SimplexOverRel` is an equivalence relation,
-- "select" all degenerate simplices,
-- and an element in each other equivalence class
instance [Fibration p] : Nonempty (Selection p) := by
  let S (n : ℕ) : Set (E _[n]) :=
    setOf (fun x ↦ ¬ (∃ (y : E.Degenerate n), SimplexOverRel p x y))
  let s (n : ℕ) : Setoid (S n) :=
    { r x y := SimplexOverRel p x.1 y.1
      iseqv := (SimplexOverRel.equivalence p n).comap Subtype.val }
  have (n : ℕ) : Function.Surjective (Quotient.mk (s n)) := Quotient.mk_surjective
  obtain ⟨σ, hσ⟩ : ∃ (σ : ({n : ℕ} → Quotient (s n) → S n)),
    ∀ (n : ℕ) (x : Quotient (s n)), Quotient.mk _ (σ x) = x :=
      ⟨fun {n} ↦ (this n).hasRightInverse.choose,
        fun {n} ↦ (this n).hasRightInverse.choose_spec⟩
  have rel {n : ℕ} (x : S n) : SimplexOverRelStruct p x.1 (σ ⟦x⟧).1 := Nonempty.some (by
    obtain ⟨h⟩ := Quotient.eq.1 (hσ _ ⟦x⟧).symm
    exact ⟨h⟩)
  let T (n : ℕ) : Set (E _[n]) := Set.range (Subtype.val ∘ σ)
  have hT {n x y} (hxy : SimplexOverRelStruct p x y) (hy : y ∈ E.Degenerate n) :
      x ∉ T n := fun hx ↦ by
    simp only [Set.mem_range, Function.comp_apply, T] at hx
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨⟨w, hw⟩, rfl⟩ := Quotient.mk_surjective z
    exact hw ⟨⟨_, hy⟩, ⟨(rel ⟨w, hw⟩).trans hxy⟩⟩
  exact ⟨
    { set n := E.Degenerate n ⊔ T n
      le_set n := le_sup_left
      unique {n x y} hx hy hxy := by
        simp only [Set.sup_eq_union, Set.mem_union] at hx hy
        obtain hx | hx := hx <;> obtain hy | hy := hy
        · exact hxy.eq_of_degenerate hx hy
        · exact (hT hxy.symm hx hy).elim
        · exact (hT hxy hy hx).elim
        · obtain ⟨x', rfl⟩ := hx
          obtain ⟨y', rfl⟩ := hy
          have := (Quotient.eq (r := s n)).2 ⟨hxy⟩
          simp only [hσ, T] at this
          rw [this]
      nonempty {n} x := by
        by_cases hx : x ∈ S n
        · exact ⟨_, Or.inr ⟨_, rfl⟩, ⟨rel ⟨x, hx⟩⟩⟩
        · simp only [Subtype.exists, exists_prop, not_exists, not_and, Set.mem_setOf_eq,
            not_forall, Classical.not_imp, not_not, S] at hx
          obtain ⟨y, hy, ⟨hxy⟩⟩ := hx
          exact ⟨y, Or.inl hy, ⟨hxy⟩⟩ }⟩

namespace Selection

variable {p} (selection : Selection p)

def SubcomplexOfSelected : Type _ :=
  Subtype (fun (Y : E.Subcomplex) ↦ ∀ (n : ℕ), Y.obj ⟨.mk n⟩ ≤ selection.set n)

instance : PartialOrder selection.SubcomplexOfSelected := by
  dsimp [SubcomplexOfSelected]
  infer_instance

instance : OrderTop selection.SubcomplexOfSelected where
  top := ⟨⨆ (A : selection.SubcomplexOfSelected), A.1, fun n ↦ by
    simp only [Subpresheaf.iSup_obj, Set.iSup_eq_iUnion, Set.le_eq_subset, Set.iUnion_subset_iff]
    intro A
    exact A.2 n⟩
  le_top A := le_iSup (ι := selection.SubcomplexOfSelected) (fun A ↦ A.1) A

def subcomplex : E.Subcomplex := (⊤ : selection.SubcomplexOfSelected).1

lemma subcomplex_obj_le (n : ℕ) : selection.subcomplex.obj ⟨.mk n⟩ ≤ selection.set n :=
  (⊤ : selection.SubcomplexOfSelected).2 n

lemma le_subcomplex (Y : selection.SubcomplexOfSelected) : Y.1 ≤ selection.subcomplex :=
  le_top (α := selection.SubcomplexOfSelected)

lemma mem_subcomplex_of_boundary {n : ℕ} (x : E _[n]) (hx : x ∈ selection.set n)
    (hx' : subcomplexBoundary n ≤ selection.subcomplex.preimage ((yonedaEquiv _ _).symm x)) :
    x ∈ selection.subcomplex.obj ⟨.mk n⟩ := by
  refine selection.le_subcomplex ⟨selection.subcomplex ⊔ Subcomplex.ofSimplex x, ?_⟩ _
    (Or.inr (Subcomplex.mem_ofSimplex_obj x))
  intro d
  simp only [Subpresheaf.max_obj, Set.le_eq_subset, Set.union_subset_iff]
  constructor
  · apply subcomplex_obj_le
  · rintro _ ⟨s, rfl⟩
    by_cases hs : s ∈ Degenerate _ _
    · exact selection.le_set _ (degenerate_map hs _)
    · rw [← mem_nondegenerate_iff_not_mem_degenerate] at hs
      obtain h | rfl := (dim_le_of_nondegenerate _ ⟨s, hs⟩ n).lt_or_eq
      · apply subcomplex_obj_le
        apply hx'
        simp only [subcomplexBoundary_obj_eq_top _ _ h, Set.top_eq_univ, Set.mem_univ]
      · rw [standardSimplex.non_degenerate_top_dim, Set.mem_singleton_iff] at hs
        simpa [hs] using hx

structure Extension where
  A : E.Subcomplex
  subcomplex_le : selection.subcomplex ≤ A
  h : (A : SSet) ⊗ Δ[1] ⟶ E
  hi' : Subcomplex.homOfLE subcomplex_le ▷ _ ≫ h = fst _ _ ≫ selection.subcomplex.ι := by aesop_cat
  r : (A : SSet) ⟶ (selection.subcomplex : SSet)
  i_r : Subcomplex.homOfLE subcomplex_le ≫ r = 𝟙 _ := by aesop_cat
  ι₀_h : ι₀ ≫ h = r ≫ selection.subcomplex.ι := by aesop_cat
  ι₁_h : ι₁ ≫ h = A.ι := by aesop_cat
  wh : h ≫ p = fst _ _ ≫ A.ι ≫ p := by aesop_cat

namespace Extension

variable {selection} (e : selection.Extension)

attribute [reassoc (attr := simp)] wh i_r ι₀_h ι₁_h

abbrev i : (selection.subcomplex : SSet) ⟶ (e.A : SSet) :=
  Subcomplex.homOfLE e.subcomplex_le

@[reassoc (attr := simp)]
lemma hi : e.i ▷ _ ≫ e.h = fst _ _ ≫ selection.subcomplex.ι := e.hi'

@[reassoc (attr := simp)]
lemma wr : e.r ≫ selection.subcomplex.ι ≫ p = e.A.ι ≫ p := by
  rw [← ι₀_h_assoc, wh, lift_fst_assoc, id_comp]

end Extension

instance : PartialOrder selection.Extension where
  le f₁ f₂ := ∃ (h : f₁.A ≤ f₂.A), f₁.h = Subcomplex.homOfLE h ▷ _ ≫ f₂.h
  le_refl f := ⟨by rfl, rfl⟩
  le_trans f₁ f₂ f₃ := by
    rintro ⟨le₁₂, fac₁₂⟩ ⟨le₂₃, fac₂₃⟩
    exact ⟨le₁₂.trans le₂₃, by rw [fac₁₂, fac₂₃]; rfl⟩
  le_antisymm := by
    rintro ⟨A₁, _, h₁, _, r₁, _, ι₀_h₁, _, _⟩ ⟨A₂, _, h₂, _, r₂, _, ι₀_h₂, _, _⟩
      ⟨le₁₂, fac₁₂⟩ ⟨le₂₁, fac₂₁⟩
    obtain rfl := le_antisymm le₁₂ le₂₁
    obtain rfl : h₁ = h₂ := fac₁₂
    obtain rfl : r₁ = r₂ := by
      rw [← cancel_mono selection.subcomplex.ι, ← ι₀_h₁, ← ι₀_h₂]
    rfl

variable {selection} in
@[reassoc]
lemma Extension.fac_r_of_le {s₁ s₂ : selection.Extension} (h : s₁ ≤ s₂) :
    Subcomplex.homOfLE h.1 ≫ s₂.r = s₁.r := by
  rw [← cancel_mono selection.subcomplex.ι, assoc, ← s₁.ι₀_h,
    h.2, ι₀_comp_assoc, s₂.ι₀_h]

variable {selection} in
lemma Extension.monotone_A : Monotone (A : selection.Extension → _) := fun _ _ h ↦ h.1

noncomputable instance : OrderBot selection.Extension where
  bot :=
    { A := selection.subcomplex
      subcomplex_le := by rfl
      h := fst _ _ ≫ selection.subcomplex.ι
      r := 𝟙 _ }
  bot_le f := ⟨f.subcomplex_le, by simp⟩

lemma exists_maximal_extension : ∃ (f : selection.Extension), IsMax f := by
  apply zorn_le
  intro S hS
  by_cases h : S.Nonempty; swap
  · simp only [Set.nonempty_def, not_exists] at h
    exact ⟨⊥, fun s hs ↦ (h s hs).elim⟩
  · let s₀ : S := ⟨h.some, h.some_mem⟩
    have : IsDirected S (· ≤ ·) := { directed := hS.directedOn.directed_val }
    let Φ : S ⥤ E.Subcomplex :=
      (Extension.monotone_A.comp (Subtype.mono_coe S)).functor
    have H := isColimitOfPreserves (Subcomplex.toPresheafFunctor)
      (CompleteLattice.isColimitCocone Φ )
    let ch : Cocone ((Φ ⋙ Subcomplex.toPresheafFunctor) ⋙ tensorRight Δ[1]) :=
      Cocone.mk E
        { app s := s.1.h
          naturality s₁ s₂ φ := by simpa using (leOfHom φ).2.symm }
    let cr : Cocone (Φ ⋙ Subcomplex.toPresheafFunctor) :=
      Cocone.mk selection.subcomplex
        { app s := s.1.r
          naturality _ _ φ := by
            simpa using (Extension.fac_r_of_le (leOfHom φ)) }
    refine ⟨{
      A := ⨆ (s : S), s.1.A
      subcomplex_le := h.some.subcomplex_le.trans (le_iSup (fun (s : S) ↦ s.1.A) _)
      h := (isColimitOfPreserves (tensorRight Δ[1]) H).desc ch
      hi' := by
        have := (isColimitOfPreserves (tensorRight Δ[1]) H).fac ch s₀
        conv_rhs at this => dsimp [ch]
        dsimp at this ⊢
        rw [← s₀.1.hi', ← this, ← MonoidalCategory.comp_whiskerRight_assoc,
          ← Subcomplex.homOfLE_comp]
      r := H.desc cr
      i_r := by
        have := H.fac cr s₀
        conv_rhs at this => dsimp [cr]
        dsimp at this
        rw [← s₀.1.i_r, ← this, Subcomplex.homOfLE_comp_assoc]
      ι₀_h := H.hom_ext (fun ⟨s, hs⟩ ↦ by
        have h₁ := H.fac cr ⟨s, hs⟩
        have h₂ := (isColimitOfPreserves (tensorRight Δ[1]) H).fac ch ⟨s, hs⟩
        dsimp [Φ] at h₁ h₂ ⊢
        rw [← ι₀_comp_assoc, reassoc_of% h₁, h₂]
        dsimp only [ch, cr]
        rw [s.ι₀_h])
      ι₁_h := H.hom_ext (fun ⟨s, hs⟩ ↦ by
        have this := (isColimitOfPreserves (tensorRight Δ[1]) H).fac ch ⟨s, hs⟩
        dsimp [Φ] at this ⊢
        rw [← ι₁_comp_assoc, this]
        dsimp only [ch, cr]
        rw [s.ι₁_h, Subcomplex.homOfLE_ι])
      wh := (isColimitOfPreserves (tensorRight Δ[1]) H).hom_ext (fun ⟨s, hs⟩ ↦ by
        have := (isColimitOfPreserves (tensorRight Δ[1]) H).fac ch ⟨s, hs⟩
        dsimp at this ⊢
        rw [reassoc_of% this]
        exact s.wh )}, fun s hs ↦ ⟨le_iSup (fun (s : S) ↦ s.1.A) ⟨s, hs⟩, ?_⟩⟩
    have := (isColimitOfPreserves (tensorRight Δ[1]) H).fac ch ⟨s, hs⟩
    dsimp at this ⊢
    simp [this, ch]

variable {selection} in
lemma Extension.A_eq_top_of_isMax (f : selection.Extension)
    (hf : IsMax f) : f.A = ⊤ := by
  ext ⟨n⟩ : 2
  simp only [top_subpresheaf_obj, Set.top_eq_univ, Set.eq_univ_iff_forall]
  induction' n using SimplexCategory.rec with n
  induction' n using Nat.strong_induction_on with n hn
  by_contra!
  obtain ⟨x, hx⟩ := this
  let f' : selection.Extension :=
    { A := f.A ⊔ .ofSimplex x
      subcomplex_le := sorry
      h := sorry
      hi' := sorry
      r := sorry
      i_r := sorry
      ι₀_h := sorry
      ι₁_h := sorry
      wh := sorry }
  have : f ≤ f' := ⟨le_sup_left, sorry⟩
  exact hx ((hf this).1 _ (Or.inr (Subcomplex.mem_ofSimplex_obj x)))

lemma exists_extension : ∃ (f : selection.Extension), f.A = ⊤ := by
  obtain ⟨f, hf⟩ := selection.exists_maximal_extension
  exact ⟨f, f.A_eq_top_of_isMax hf⟩

noncomputable def extension : selection.Extension := selection.exists_extension.choose

@[simp]
lemma extension_A : selection.extension.A = ⊤ := selection.exists_extension.choose_spec

noncomputable def relativeDeformationRetract :
    selection.subcomplex.RelativeDeformationRetract p where
  i := selection.subcomplex.ι
  i_eq_ι := rfl
  r := (Subcomplex.topIso E).inv ≫ (Subcomplex.isoOfEq (by simp)).inv ≫ selection.extension.r
  retract := selection.extension.i_r
  h := ((Subcomplex.topIso E).inv ≫ (Subcomplex.isoOfEq (by simp)).inv) ▷ _ ≫
      selection.extension.h
  hi := selection.extension.hi
  h₀ := by
    dsimp
    rw [ι₀_comp_assoc, assoc, assoc, assoc, Extension.ι₀_h]
  h₁ := by
    dsimp
    rw [ι₁_comp_assoc, assoc, Extension.ι₁_h]
    rfl
  wr := by
    dsimp
    rw [assoc, assoc, Extension.wr]
    rfl
  wh := by
    dsimp
    rw [assoc, Extension.wh]
    rfl

instance [Fibration p] :
    Fibration (C := SSet) (selection.subcomplex.ι ≫ p) := by
  rw [fibration_iff]
  apply MorphismProperty.of_retract selection.relativeDeformationRetract.retractArrow
  rwa [← fibration_iff]

instance minimalFibration_ι_comp [Fibration p] :
    MinimalFibration (selection.subcomplex.ι ≫ p) where
  minimal {n x y} h := by
    simpa [← Subtype.ext_iff] using selection.unique
      (selection.subcomplex_obj_le _ x.2) (selection.subcomplex_obj_le _ y.2)
      (h.map selection.relativeDeformationRetract.retractArrow.i rfl rfl)

end Selection

end MinimalFibration

end SSet
