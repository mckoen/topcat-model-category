/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.MorphismProperty.Limits
import TopCatModelCategory.ColimitsType
import TopCatModelCategory.CommSq
import TopCatModelCategory.SSet.Basic


/-!
# Subcomplexes of simplicial sets

-/

universe u

open CategoryTheory MonoidalCategory Simplicial Limits Opposite

namespace CategoryTheory
-- GrothendieckTopology.Subpresheaf should be moved...

variable {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*)

instance : CompleteLattice (Subpresheaf P) where
  sup F G :=
    { obj U := F.obj U ⊔ G.obj U
      map _ _ := by
        rintro (h|h)
        · exact Or.inl (F.map _ h)
        · exact Or.inr (G.map _ h) }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by
    rintro x (h|h)
    · exact h₁ _ h
    · exact h₂ _ h
  inf S T :=
    { obj U := S.obj U ⊓ T.obj U
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩}
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj U := sSup (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        obtain ⟨_, ⟨F, h, rfl⟩, h'⟩ := hx
        simp only [Set.sSup_eq_sUnion, Set.sUnion_image, Set.preimage_iUnion,
          Set.mem_iUnion, Set.mem_preimage, exists_prop]
        exact ⟨_, h, F.map f h'⟩ }
  le_sSup _ _ _ _ _ := by aesop
  sSup_le _ _ _ _ _ := by aesop
  sInf S :=
    { obj U := sInf (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        rintro _ ⟨F, h, rfl⟩
        exact F.map f (hx _ ⟨_, h, rfl⟩) }
  sInf_le _ _ _ _ _ := by aesop
  le_sInf _ _ _ _ _ := by aesop
  bot :=
    { obj U := ⊥
      map := by simp }
  le_top _ _ := le_top
  bot_le _ _ := bot_le

namespace Subpresheaf

@[simp] lemma top_obj (i : Cᵒᵖ) : (⊤ : Subpresheaf P).obj i = ⊤ := rfl
@[simp] lemma bot_obj (i : Cᵒᵖ) : (⊥ : Subpresheaf P).obj i = ⊥ := rfl

variable {P}

lemma sSup_obj (S : Set (Subpresheaf P)) (U : Cᵒᵖ) :
    (sSup S).obj U = sSup (Set.image (fun T ↦ T.obj U) S) := rfl

@[simp]
lemma iSup_obj {ι : Type*} (S : ι → Subpresheaf P) (U : Cᵒᵖ) :
    (iSup S).obj U = iSup (fun i ↦ (S i).obj U) := by
  simp [iSup, sSup_obj]

lemma sInf_obj (S : Set (Subpresheaf P)) (U : Cᵒᵖ) :
    (sInf S).obj U = sInf (Set.image (fun T ↦ T.obj U) S) := rfl

@[simp]
lemma iInf_obj {ι : Type*} (S : ι → Subpresheaf P) (U : Cᵒᵖ) :
    (iInf S).obj U = iInf (fun i ↦ (S i).obj U) := by
  simp [iInf, sInf_obj]

lemma le_def (S T : Subpresheaf P) : S ≤ T ↔ ∀ U, S.obj U ≤ T.obj U := Iff.rfl

@[simp]
lemma max_obj (S T : Subpresheaf P) (i : Cᵒᵖ) :
    (S ⊔ T).obj i = S.obj i ∪ T.obj i := rfl

@[simp]
lemma min_obj (S T : Subpresheaf P) (i : Cᵒᵖ) :
    (S ⊓ T).obj i = S.obj i ∩ T.obj i := rfl

lemma max_min (S₁ S₂ T : Subpresheaf P) :
    (S₁ ⊔ S₂) ⊓ T = (S₁ ⊓ T) ⊔ (S₂ ⊓ T) := by
  aesop

lemma iSup_min {ι : Type*} (S : ι → Subpresheaf P) (T : Subpresheaf P) :
    iSup S ⊓ T = ⨆ i, S i ⊓ T := by
  aesop

end Subpresheaf

end CategoryTheory

namespace SSet

variable {X Y : SSet.{u}}

@[simp]
lemma braiding_hom_apply_fst {n : SimplexCategoryᵒᵖ} (x : (X ⊗ Y).obj n) :
    ((β_ X Y).hom.app n x).1 = x.2 := rfl

@[simp]
lemma braiding_hom_apply_snd {n : SimplexCategoryᵒᵖ} (x : (X ⊗ Y).obj n) :
    ((β_ X Y).hom.app n x).2 = x.1 := rfl

@[simp]
lemma braiding_inv_apply_fst {n : SimplexCategoryᵒᵖ} (x : (Y ⊗ X).obj n) :
    ((β_ X Y).inv.app n x).1 = x.2 := rfl

@[simp]
lemma braiding_inv_apply_snd {n : SimplexCategoryᵒᵖ} (x : (Y ⊗ X).obj n) :
    ((β_ X Y).inv.app n x).2 = x.1 := rfl

variable (X Y)

protected abbrev Subcomplex := Subpresheaf X

namespace Subcomplex

instance : CompleteLattice X.Subcomplex :=
  inferInstance

variable {X Y}

variable (S : X.Subcomplex) (T : Y.Subcomplex)

instance : CoeOut X.Subcomplex SSet.{u} where
  coe := fun S ↦ S.toPresheaf

variable (X)

@[simps!]
def topIso : ((⊤ : X.Subcomplex) : SSet) ≅ X :=
  NatIso.ofComponents (fun n ↦ (Equiv.Set.univ (X.obj n)).toIso)

@[reassoc (attr := simp)]
lemma topIso_inv_ι : (topIso X).inv ≫ Subpresheaf.ι _ = 𝟙 _ := rfl

def isInitialBot : IsInitial ((⊥ : X.Subcomplex) : SSet.{u}) :=
  IsInitial.ofUniqueHom (fun P ↦
    { app i := fun ⟨x, hx⟩ ↦ by simp at hx
      naturality i j f := by ext ⟨x, hx⟩; simp at hx })
    (fun _ _ ↦ by ext _ ⟨x, hx⟩; simp at hx)

variable {X}

variable {S} in
@[ext]
lemma coe_ext {Δ : SimplexCategoryᵒᵖ} {x y : S.obj Δ} (h : x.val = y.val) : x = y :=
  Subtype.ext h

lemma sSup_obj (S : Set X.Subcomplex) (n : SimplexCategoryᵒᵖ) :
    (sSup S).obj n = sSup (Set.image (fun T ↦ T.obj n) S) := rfl

@[simp]
lemma iSup_obj {ι : Type*} (S : ι → X.Subcomplex) (n : SimplexCategoryᵒᵖ) :
    (iSup S).obj n = iSup (fun i ↦ (S i).obj n) := by
  simp [iSup, sSup_obj]

lemma iSup_inf {ι : Type*} (S : ι → X.Subcomplex) (T : X.Subcomplex):
    (⨆ i, S i) ⊓ T = ⨆ i, (S i ⊓ T)  := by
  aesop

instance :
    letI src : SSet := S
    letI f : src ⟶ _ := S.ι
    Mono f := by
  change Mono S.ι
  infer_instance

@[simp]
lemma ι_app {Δ : SimplexCategoryᵒᵖ} (x : S.obj Δ) :
    S.ι.app Δ x = x.val := rfl

instance : Mono S.ι := by
  infer_instance

@[simps]
noncomputable def prod : (X ⊗ Y).Subcomplex where
  obj Δ := (S.obj Δ).prod (T.obj Δ)
  map i _ hx := ⟨S.map i hx.1, T.map i hx.2⟩

lemma prod_monotone {S₁ S₂ : X.Subcomplex} (hX : S₁ ≤ S₂) {T₁ T₂ : Y.Subcomplex} (hY : T₁ ≤ T₂) :
    S₁.prod T₁ ≤ S₂.prod T₂ :=
  fun _ _ hx => ⟨hX _ hx.1, hY _ hx.2⟩

example : PartialOrder X.Subcomplex := inferInstance
example : SemilatticeSup X.Subcomplex := inferInstance

section

variable {S₁ S₂ : X.Subcomplex} (h : S₁ ≤ S₂)

def homOfLE : (S₁ : SSet.{u}) ⟶ (S₂ : SSet.{u}) := Subpresheaf.homOfLe h

@[simp]
lemma homOfLE_app_val (Δ : SimplexCategoryᵒᵖ) (x : S₁.obj Δ) :
    ((homOfLE h).app Δ x).val = x.val := rfl

@[reassoc (attr := simp)]
lemma homOfLE_ι : homOfLE h ≫ S₂.ι = S₁.ι := rfl

instance mono_homOfLE : Mono (homOfLE h) := mono_of_mono_fac (homOfLE_ι h)

end

@[simps]
def toPresheafFunctor : X.Subcomplex ⥤ SSet.{u} where
  obj S := S
  map h := homOfLE (leOfHom h)

section

variable {S₁ S₂ : X.Subcomplex} (h : S₁ = S₂)

@[simps]
def isoOfEq : (S₁ : SSet.{u}) ≅ (S₂ : SSet.{u}) where
  hom := homOfLE (by rw [h])
  inv := homOfLE (by rw [h])

end

variable (X) in
@[simps]
def forget : X.Subcomplex ⥤ SSet.{u} where
  obj S := S
  map f := homOfLE (leOfHom f)

noncomputable def unionProd : (X ⊗ Y).Subcomplex := ((⊤ : X.Subcomplex).prod T) ⊔ (S.prod ⊤)

lemma mem_unionProd_iff {n : SimplexCategoryᵒᵖ} (x : (X ⊗ Y).obj n) :
    x ∈ (unionProd S T).obj _ ↔ x.1 ∈ S.obj _ ∨ x.2 ∈ T.obj _ := by
  dsimp [unionProd, Set.prod]
  aesop

lemma top_prod_le_unionProd : (⊤ : X.Subcomplex).prod T ≤ S.unionProd T := le_sup_left

lemma prod_top_le_unionProd : (S.prod ⊤) ≤ S.unionProd T := le_sup_right

lemma prod_le_top_prod : S.prod T ≤ (⊤ : X.Subcomplex).prod T :=
  prod_monotone le_top (by rfl)

lemma prod_le_prod_top : S.prod T ≤ S.prod ⊤ :=
  prod_monotone (by rfl) le_top

lemma prod_le_unionProd : S.prod T ≤ S.unionProd T :=
  (prod_le_prod_top S T).trans (prod_top_le_unionProd S T)

end Subcomplex

def subcomplexBoundary (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex where
  obj _ s := ¬Function.Surjective (asOrderHom s)
  map φ s hs := ((boundary n).map φ ⟨s, hs⟩).2

lemma subcomplexBoundary_toSSet (n : ℕ) : subcomplexBoundary.{u} n = ∂Δ[n] := rfl

lemma subcomplexBoundary_ι (n : ℕ) :
    (subcomplexBoundary.{u} n).ι = boundaryInclusion n := rfl

@[simps]
def subcomplexHorn (n : ℕ) (i : Fin (n + 1)) : (Δ[n] : SSet.{u}).Subcomplex where
  obj _ s := Set.range (asOrderHom s) ∪ {i} ≠ Set.univ
  map φ s hs := ((horn n i).map φ ⟨s, hs⟩).2

lemma mem_subcomplexHorn_iff {n : ℕ} (i : Fin (n + 1)) {m : SimplexCategoryᵒᵖ}
    (x : (Δ[n] : SSet.{u}).obj m) :
    x ∈ (subcomplexHorn n i).obj m ↔ Set.range (asOrderHom x) ∪ {i} ≠ Set.univ := Iff.rfl

lemma subcomplexHorn_toSSet (n : ℕ) (i : Fin (n + 1)) :
    subcomplexHorn.{u} n i = Λ[n, i] := rfl

lemma subcomplexHorn_ι (n : ℕ) (i : Fin (n + 1)) :
    (subcomplexHorn.{u} n i).ι = hornInclusion n i := rfl

@[simp]
lemma subcomplexBoundary_zero : subcomplexBoundary.{u} 0 = ⊥ := by
  ext m x
  simp [subcomplexBoundary]
  apply not_not.2
  intro x
  fin_cases x
  refine ⟨0, ?_⟩
  apply Subsingleton.elim

section

variable {X Y}
variable (f : X ⟶ Y)

attribute [local simp] FunctorToTypes.naturality

@[simps]
def Subcomplex.range : Y.Subcomplex where
  obj Δ := Set.range (f.app Δ)
  map := by
    rintro Δ Δ' φ _ ⟨x, rfl⟩
    exact ⟨X.map φ x, by simp⟩

@[simp]
lemma Subcomplex.range_ι (A : X.Subcomplex) :
    range A.ι = A := by
  aesop

def toRangeSubcomplex : X ⟶ Subcomplex.range f where
  app Δ x := ⟨f.app Δ x, ⟨x, rfl⟩⟩

@[simp]
lemma toRangeSubcomplex_apply_val {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ) :
    ((toRangeSubcomplex f).app Δ x).val = f.app Δ x := rfl

@[reassoc (attr := simp)]
lemma toRangeSubcomplex_ι : toRangeSubcomplex f ≫ (Subcomplex.range f).ι = f := rfl

instance : Epi (toRangeSubcomplex f) := by
  have (n) : Epi ((toRangeSubcomplex f).app n) := by
    rw [epi_iff_surjective]
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  apply NatTrans.epi_of_epi_app

instance : Balanced SSet.{u} :=
  inferInstanceAs (Balanced (SimplexCategoryᵒᵖ ⥤ Type u))

instance {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] : IsIso (toRangeSubcomplex f) := by
  have := mono_of_mono_fac (toRangeSubcomplex_ι f)
  apply isIso_of_mono_of_epi

lemma Subcomplex.range_eq_top_iff : Subcomplex.range f = ⊤ ↔ Epi f := by
  rw [NatTrans.epi_iff_epi_app, Subpresheaf.ext_iff, funext_iff]
  simp only [epi_iff_surjective, range_obj, top_subpresheaf_obj, Set.top_eq_univ,
    Set.range_eq_univ]

lemma Subcomplex.range_eq_top [Epi f] : Subcomplex.range f = ⊤ := by
  rwa [range_eq_top_iff]

end

namespace Subcomplex

variable {X}
def Sq (A₁ A₂ A₃ A₄ : X.Subcomplex) := Lattice.BicartSq A₁ A₂ A₃ A₄

namespace Sq

variable {A₁ A₂ A₃ A₄ : X.Subcomplex} (sq : Sq A₁ A₂ A₃ A₄)

include sq

lemma le₁₂ : A₁ ≤ A₂ := by rw [← sq.min_eq]; exact inf_le_left
lemma le₁₃ : A₁ ≤ A₃ := by rw [← sq.min_eq]; exact inf_le_right
lemma le₂₄ : A₂ ≤ A₄ := by rw [← sq.max_eq]; exact le_sup_left
lemma le₃₄ : A₃ ≤ A₄ := by rw [← sq.max_eq]; exact le_sup_right

-- the associated commutative square in `SSet`, which is both pushout and pullback
lemma commSq : CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) := ⟨rfl⟩

lemma obj (n : SimplexCategoryᵒᵖ) :
    Lattice.BicartSq (A₁.obj n) (A₂.obj n) (A₃.obj n) (A₄.obj n) where
  max_eq := by
    rw [← sq.max_eq]
    rfl
  min_eq := by
    rw [← sq.min_eq]
    rfl

lemma isPushout : IsPushout (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) where
  w := rfl
  isColimit' := ⟨by
    refine evaluationJointlyReflectsColimits _ (fun n ↦ ?_)
    exact (PushoutCocone.isColimitMapCoconeEquiv _ _).2
      (Types.isColimitPushoutCoconeOfBicartSqOfSets (sq.obj n))⟩

end Sq

section

variable {Y}
@[simps]
def preimage (A : X.Subcomplex) (p : Y ⟶ X) : Y.Subcomplex where
  obj n := p.app n ⁻¹' (A.obj n)
  map f := (Set.preimage_mono (A.map f)).trans (by
    simp only [Set.preimage_preimage, FunctorToTypes.naturality _ _ p f]
    rfl)

@[simp]
lemma preimage_max (A B : X.Subcomplex) (p : Y ⟶ X) :
    (A ⊔ B).preimage p = A.preimage p ⊔ B.preimage p := rfl

@[simp]
lemma preimage_min (A B : X.Subcomplex) (p : Y ⟶ X) :
    (A ⊓ B).preimage p = A.preimage p ⊓ B.preimage p := rfl

@[simp]
lemma preimage_iSup {ι : Type*} (A : ι → X.Subcomplex) (p : Y ⟶ X) :
    (⨆ i, A i).preimage p = ⨆ i, (A i).preimage p := by aesop

@[simp]
lemma preimage_iInf {ι : Type*} (A : ι → X.Subcomplex) (p : Y ⟶ X) :
    (⨅ i, A i).preimage p = ⨅ i, (A i).preimage p := by aesop

@[simps]
def fromPreimage (A : X.Subcomplex) (p : Y ⟶ X) :
    (A.preimage p : SSet) ⟶ (A : SSet) where
  app Δ y := ⟨p.app _ y.1, y.2⟩
  naturality _ _ f := by
    ext ⟨y, hy⟩
    dsimp
    ext
    exact FunctorToTypes.naturality _ _ p f y

def ofSimplex {n : ℕ} (x : X _[n]) : X.Subcomplex :=
  range ((X.yonedaEquiv (.mk n)).symm x)

@[simp]
lemma range_eq_ofSimplex {n : ℕ} (f : Δ[n] ⟶ X) :
    range f = ofSimplex (X.yonedaEquiv _ f) := by
  simp [ofSimplex]

lemma mem_ofSimplex_obj {n : ℕ} (x : X _[n]) : x ∈ (ofSimplex x).obj _ := by
  refine ⟨standardSimplex.objMk .id, ?_⟩
  obtain ⟨x, rfl⟩ := (X.yonedaEquiv _).surjective x
  rw [Equiv.symm_apply_apply]
  rfl

lemma ofSimplex_le_iff {n : ℕ} (x : X _[n]) (A : X.Subcomplex) :
    ofSimplex x ≤ A ↔ x ∈ A.obj _ := by
  constructor
  · intro h
    apply h
    apply mem_ofSimplex_obj
  · rintro h m _ ⟨y, rfl⟩
    obtain ⟨f, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective y
    exact A.map f.op h

lemma le_ofSimplex_iff (x : X _[0]) (A : X.Subcomplex) :
    A ≤ ofSimplex x ↔ A.ι = const x := by
  constructor
  · intro h
    ext m ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := h _ hx
    simp
  · intro h
    rw [← A.range_ι, h]
    rintro m _ ⟨y, rfl⟩
    rw [const_app]
    exact Subpresheaf.map _ _ (mem_ofSimplex_obj x)

end

section

variable {Y} (S : X.Subcomplex) (f : X ⟶ Y)

@[simps]
def image : Y.Subcomplex where
  obj Δ := (f.app Δ) '' (S.obj Δ)
  map := by
    rintro Δ Δ' φ _ ⟨x, hx, rfl⟩
    exact ⟨X.map φ x, S.map φ hx, by apply FunctorToTypes.naturality⟩

lemma app_mem_image {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ) (hx : x ∈ S.obj _):
    f.app _ x ∈ (S.image f).obj _ :=
  ⟨x, hx, rfl⟩

lemma image_le_iff (Z : Y.Subcomplex) :
    S.image f ≤ Z ↔ S ≤ Z.preimage f := by
  simp [Subpresheaf.le_def]

lemma image_top : (⊤ : X.Subcomplex).image f = range f := by aesop

lemma image_comp {Z : SSet.{u}} (g : Y ⟶ Z) :
    S.image (f ≫ g) = (S.image f).image g := by aesop

lemma range_comp {Z : SSet.{u}} (g : Y ⟶ Z) :
    Subcomplex.range (f ≫ g) = (Subcomplex.range f).image g := by
  simp only [← image_top, image_comp]

lemma image_iSup {ι : Type*} (S : ι → X.Subcomplex) (f : X ⟶ Y) :
    image (⨆ i, S i) f = ⨆ i, (S i).image f := by
  aesop

@[simp]
lemma image_ofSimplex {n : ℕ} (x : X _[n]) (f : X ⟶ Y) :
    (ofSimplex x).image f = ofSimplex (f.app _ x) := by
  apply le_antisymm
  · rw [image_le_iff, ofSimplex_le_iff, preimage_obj, Set.mem_preimage]
    apply mem_ofSimplex_obj
  · rw [ofSimplex_le_iff]
    exact ⟨x, mem_ofSimplex_obj _, rfl⟩

def toImage : (S : SSet) ⟶ (S.image f : SSet) :=
  (S.image f).lift (S.ι ≫ f) (by aesop)

@[reassoc (attr := simp)]
lemma toImage_ι : S.toImage f ≫ (S.image f).ι = S.ι ≫ f := rfl

instance : Epi (S.toImage f) := by
  rw [← range_eq_top_iff]
  apply le_antisymm (by simp)
  rintro m ⟨_, ⟨y, hy, rfl⟩⟩ _
  exact ⟨⟨y, hy⟩, rfl⟩

end

section

lemma _root_.Set.preimage_eq_iff {X Y : Type*} (f : X → Y)
    (hf : Function.Injective f) (A : Set X) (B : Set Y) :
    B.preimage f = A ↔ B ⊓ Set.range f = A.image f := by
  constructor
  · aesop
  · intro h
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hx⟩ : f x ∈ f '' A := by
        rw [← h]
        exact ⟨hx, by aesop⟩
      simpa only [← hf hx] using hy
    · intro hx
      have : f '' A ≤ B := by
        rw [← h]
        exact inf_le_left
      apply this
      aesop

lemma preimage_eq_iff {X Y : SSet.{u}}
    (f : X ⟶ Y) (A : X.Subcomplex) (B : Y.Subcomplex) [Mono f] :
    B.preimage f = A ↔ B ⊓ Subcomplex.range f = A.image f := by
  simp only [Subpresheaf.ext_iff, funext_iff]
  apply forall_congr'
  intro i
  apply Set.preimage_eq_iff
  rw [← mono_iff_injective]
  infer_instance

lemma preimage_eq_top_iff {X Y : SSet.{u}}
    (f : X ⟶ Y) (B : Y.Subcomplex) [Mono f] :
    B.preimage f = ⊤ ↔ range f ≤ B := by
  rw [preimage_eq_iff, image_top, inf_eq_right]

@[simp]
lemma preimage_image_of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) (B : Y.Subcomplex) [IsIso f] :
    (B.preimage f).image f = B := by
  apply le_antisymm
  · rw [image_le_iff]
  · intro n y hy
    exact ⟨(inv f).app _ y, by simpa [← FunctorToTypes.comp]⟩

end

section

variable {Y} (f : X ⟶ Y) {B : Y.Subcomplex} (hf : B.preimage f = ⊤)

def lift : X ⟶ B :=
  (topIso X).inv ≫ homOfLE (by simp [hf]) ≫ B.fromPreimage f

@[reassoc (attr := simp)]
lemma lift_ι : lift f hf ≫ B.ι = f := rfl

@[simp]
lemma lift_app_coe {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    ((lift f g).app _ x).1 = f.app _ x := rfl

end

section

variable {n : ℕ} (x : X _[n])

def toOfSimplex : Δ[n] ⟶ ofSimplex x :=
  Subcomplex.lift ((yonedaEquiv _ _).symm x) (by
    apply le_antisymm (by simp)
    rw [← image_le_iff, image_top, range_eq_ofSimplex, Equiv.apply_symm_apply])

@[reassoc (attr := simp)]
def toOfSimplex_ι :
    toOfSimplex x ≫ (ofSimplex x).ι = (yonedaEquiv _ _).symm x := rfl

instance : Epi (toOfSimplex x) := by
  rw [← range_eq_top_iff]
  ext m ⟨_, u, rfl⟩
  simp only [Subpresheaf.toPresheaf_obj, range_eq_ofSimplex, top_subpresheaf_obj, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  exact ⟨u, by simp; rfl⟩

lemma isIso_toOfSimplex_iff :
    IsIso (toOfSimplex x) ↔ Mono ((yonedaEquiv _ _).symm x) := by
  constructor
  · intro
    rw [← toOfSimplex_ι]
    infer_instance
  · intro h
    have := mono_of_mono_fac (toOfSimplex_ι x)
    apply isIso_of_mono_of_epi

end

section

variable {Y} (f : Y ⟶ X) (A B : X.Subcomplex) (A' B' : Y.Subcomplex)
    (hA' : A' = A.preimage f ⊓ B')
    (hB : B = A ⊔ B'.image f)

namespace pushoutCoconeOfPullback

variable {f A A' B'}

@[simps!]
def g₁ : (A' : SSet) ⟶ (A : SSet) :=
  homOfLE (by simpa only [hA'] using inf_le_left) ≫ A.fromPreimage f

@[simps!]
def g₂ : (A' : SSet) ⟶ (B' : SSet) :=
  homOfLE (by simpa only [hA'] using inf_le_right)

end pushoutCoconeOfPullback

open pushoutCoconeOfPullback

@[simps!]
def pushoutCoconeOfPullback : PushoutCocone (g₁ hA') (g₂ hA') :=
  PushoutCocone.mk (W := (B : SSet)) (homOfLE (by simpa only [hB] using le_sup_left))
    (homOfLE (by simpa only [← image_le_iff, hB] using le_sup_right) ≫ B.fromPreimage f) rfl

noncomputable def isColimitPushoutCoconeOfPullback [hf : Mono f] :
    IsColimit (pushoutCoconeOfPullback f A B A' B' hA' hB) :=
  evaluationJointlyReflectsColimits _ (fun n ↦
    (PushoutCocone.isColimitMapCoconeEquiv _ _).2
      (Types.isColimitPushoutCoconeOfPullbackSets (f := f.app n)
      (A.obj n) (B.obj n) (A'.obj n) (B'.obj n) (by rw [hA']; rfl) (by rw [hB]; rfl)
        (by
          rw [NatTrans.mono_iff_mono_app] at hf
          simp only [mono_iff_injective] at hf
          rintro ⟨x₁, _⟩ ⟨x₂, _⟩ h
          simpa only [Subtype.mk.injEq] using hf n h)))

end

variable {Y} in
noncomputable def prodIso (S : X.Subcomplex) (T : Y.Subcomplex) :
    (S.prod T : SSet) ≅ (S : SSet) ⊗ (T : SSet) where
  hom := ChosenFiniteProducts.lift
    (lift ((S.prod T).ι ≫ ChosenFiniteProducts.fst _ _) (by
      ext n ⟨x, h⟩
      simpa using h.1))
    (lift ((S.prod T).ι ≫ ChosenFiniteProducts.snd _ _) (by
      ext n ⟨x, h⟩
      simpa using h.2))
  inv := lift (S.ι ⊗ T.ι) (by
    ext n ⟨x, y⟩
    dsimp
    simp only [Set.mem_preimage, tensorHom_app_apply, Subpresheaf.ι_app,
      Set.mem_univ, iff_true]
    exact ⟨x.2, y.2⟩)

namespace unionProd

variable {Y} (S : X.Subcomplex) (T : Y.Subcomplex)

noncomputable def ι₁ : X ⊗ T ⟶ unionProd S T :=
  lift (X ◁ T.ι) (by
    ext m ⟨x₁, x₂⟩
    simp [unionProd, Set.prod]
    exact Or.inl x₂.2)

noncomputable def ι₂ : (S : SSet.{u}) ⊗ Y ⟶ (unionProd S T : SSet.{u}) :=
  lift (S.ι ▷ Y) (by
    ext m ⟨x₁, x₂⟩
    simp [unionProd, Set.prod]
    exact Or.inr x₁.2)

@[reassoc (attr := simp)]
lemma ι₁_ι : ι₁ S T ≫ (unionProd S T).ι = X ◁ T.ι := rfl

@[reassoc (attr := simp)]
lemma ι₂_ι : ι₂ S T ≫ (unionProd S T).ι = S.ι ▷ Y := rfl

lemma sq : Sq (S.prod T) ((⊤ : X.Subcomplex).prod T) (S.prod ⊤) (unionProd S T) where
  max_eq := rfl
  min_eq := by
    ext n ⟨x, y⟩
    change _ ∧ _ ↔ _
    simp [prod, Set.prod, Membership.mem, Set.Mem, setOf]
    tauto

lemma isPushout : IsPushout (S.ι ▷ (T : SSet)) ((S : SSet) ◁ T.ι)
    (unionProd.ι₁ S T) (unionProd.ι₂ S T) :=
  (sq S T).isPushout.of_iso
    (Subcomplex.prodIso _ _)
    (Subcomplex.prodIso _ _ ≪≫ MonoidalCategory.whiskerRightIso (topIso X) _)
    (Subcomplex.prodIso _ _ ≪≫ MonoidalCategory.whiskerLeftIso _ (topIso Y))
    (Iso.refl _) rfl rfl rfl rfl

@[simp]
lemma preimage_β_hom : (unionProd S T).preimage (β_ _ _).hom = unionProd T S := by
  ext n ⟨x, y⟩
  simp only [mem_unionProd_iff, preimage_obj, Set.mem_preimage,
    braiding_hom_apply_fst, braiding_hom_apply_snd]
  tauto

@[simp]
lemma preimage_β_inv : (unionProd S T).preimage (β_ _ _).inv = unionProd T S := by
  apply preimage_β_hom

@[simp]
lemma image_β_hom : (unionProd S T).image (β_ _ _).hom = unionProd T S := by
  rw [← preimage_β_hom, preimage_image_of_isIso]

@[simp]
lemma image_β_inv : (unionProd S T).image (β_ _ _).hom = unionProd T S := by
  apply image_β_hom


noncomputable def symmIso : (unionProd S T : SSet) ≅ (unionProd T S : SSet) where
  hom := lift ((unionProd S T).ι ≫ (β_ _ _).hom) (by
    rw [Subcomplex.preimage_eq_top_iff, range_comp, Subcomplex.range_ι, image_β_hom])
  inv := lift ((unionProd T S).ι ≫ (β_ _ _).hom) (by
    rw [Subcomplex.preimage_eq_top_iff, range_comp, Subcomplex.range_ι, image_β_hom])

end unionProd

section multicoequalizer

variable {A : X.Subcomplex} {ι : Type*}
  {U : ι → X.Subcomplex} {V : ι → ι → X.Subcomplex}
  (h : CompleteLattice.MulticoequalizerDiagram A U V)

noncomputable def multicoforkIsColimit :
    IsColimit (h.multicofork.map toPresheafFunctor) :=
  evaluationJointlyReflectsColimits _ (fun n ↦ by
    have h' : CompleteLattice.MulticoequalizerDiagram (A.obj n) (fun i ↦ (U i).obj n)
        (fun i j ↦ (V i j).obj n) :=
      { hX := by simp [h.hX]
        hV := by simp [h.hV] }
    exact (isColimitMapMulticoforkEquiv _ _).2 (Types.isColimitMulticoforkMapSetToTypes h'))

noncomputable def multicoforkIsColimit' [LinearOrder ι] :
    IsColimit (h.multicofork'.map toPresheafFunctor) :=
  evaluationJointlyReflectsColimits _ (fun n ↦ by
    have h' : CompleteLattice.MulticoequalizerDiagram (A.obj n) (fun i ↦ (U i).obj n)
        (fun i j ↦ (V i j).obj n) :=
      { hX := by simp [h.hX]
        hV := by simp [h.hV] }
    exact (isColimitMapMulticoforkEquiv _ _).2 (Types.isColimitMulticoforkMapSetToTypes' h'))

end multicoequalizer

variable {Y}

lemma hom_ext (B : Y.Subcomplex) {f g : X ⟶ B} (h : f ≫ B.ι = g ≫ B.ι): f = g := by
  simpa only [cancel_mono] using h

lemma hom_ext_of_eq_bot {A : X.Subcomplex} (h : A = ⊥) {f g : (A : SSet) ⟶ Y} : f = g := by
  ext _ ⟨x, hx⟩
  simp [h] at hx

end Subcomplex

end SSet
