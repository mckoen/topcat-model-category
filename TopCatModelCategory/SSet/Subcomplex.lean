/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.MorphismProperty.Limits
import TopCatModelCategory.ColimitsType


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

lemma sSup_obj (S : Set (Subpresheaf P)) (U : Cᵒᵖ) :
    (sSup S).obj U = sSup (Set.image (fun T ↦ T.obj U) S) := rfl

@[simp]
lemma iSup_obj {ι : Type*} (S : ι → Subpresheaf P) (U : Cᵒᵖ) :
    (iSup S).obj U = iSup (fun i ↦ (S i).obj U) := by
  simp [iSup, sSup_obj]

lemma Subpresheaf.le_def (S T : Subpresheaf P) : S ≤ T ↔ ∀ U, S.obj U ≤ T.obj U := Iff.rfl

end CategoryTheory

namespace SSet

variable (X Y : SSet.{u})

protected abbrev Subcomplex := Subpresheaf X

namespace Subcomplex

instance : CompleteLattice X.Subcomplex :=
  inferInstance

variable {X Y}

variable (S : X.Subcomplex) (T : Y.Subcomplex)

instance : CoeOut X.Subcomplex SSet.{u} where
  coe := fun S ↦ S.toPresheaf

variable (X) in
@[simps!]
def topIso : ((⊤ : X.Subcomplex) : SSet) ≅ X :=
  NatIso.ofComponents (fun n ↦  (Equiv.Set.univ (X.obj n)).toIso)

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

variable {Y} (S : X.Subcomplex) (T : Y.Subcomplex)

lemma unionProd_sq : Sq (S.prod T) ((⊤ : X.Subcomplex).prod T) (S.prod ⊤) (unionProd S T) where
  max_eq := rfl
  min_eq := by
    ext n ⟨x, y⟩
    change _ ∧ _ ↔ _
    simp [prod, Set.prod, Membership.mem, Set.Mem, setOf]
    tauto

@[simps]
def preimage (A : X.Subcomplex) (p : Y ⟶ X) : Y.Subcomplex where
  obj n := p.app n ⁻¹' (A.obj n)
  map f := (Set.preimage_mono (A.map f)).trans (by
    simp only [Set.preimage_preimage, FunctorToTypes.naturality _ _ p f]
    rfl)

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

lemma mem_ofSimplex_obj {n : ℕ} (x : X _[n]) : x ∈ (ofSimplex x).obj _ := by
  refine ⟨standardSimplex.objMk .id, ?_⟩
  obtain ⟨x, rfl⟩ := (X.yonedaEquiv _).surjective x
  rw [Equiv.symm_apply_apply]
  rfl

@[simp]
lemma ofSimplex_le_iff {n : ℕ} (x : X _[n]) (A : X.Subcomplex) :
    ofSimplex x ≤ A ↔ x ∈ A.obj _ := by
  constructor
  · intro h
    apply h
    apply mem_ofSimplex_obj
  · rintro h m _ ⟨y, rfl⟩
    obtain ⟨f, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective y
    exact A.map f.op h

end

section

variable {Y} (S : X.Subcomplex) (f : X ⟶ Y)

@[simps]
def image : Y.Subcomplex where
  obj Δ := (f.app Δ) '' (S.obj Δ)
  map := by
    rintro Δ Δ' φ _ ⟨x, hx, rfl⟩
    exact ⟨X.map φ x, S.map φ hx, by apply FunctorToTypes.naturality⟩

lemma image_le_iff (Z : Y.Subcomplex) :
    S.image f ≤ Z ↔ S ≤ Z.preimage f := by
  simp [Subpresheaf.le_def]

lemma image_top : (⊤ : X.Subcomplex).image f = range f := by aesop

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

end Subcomplex

end SSet
