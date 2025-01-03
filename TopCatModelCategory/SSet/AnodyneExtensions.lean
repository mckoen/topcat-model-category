import TopCatModelCategory.SSet.Boundary
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

open CategoryTheory Limits

universe w v u
namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

class IsGabrielZismanSaturated (W : MorphismProperty C) : Prop where
  isMultiplicative : W.IsMultiplicative := by infer_instance
  isStableUnderCobaseChange : W.IsStableUnderCobaseChange := by infer_instance
  isStableUnderRetracts : W.IsStableUnderRetracts := by infer_instance
  isStableUnderCoproductsOfShape (J : Type w) : W.IsStableUnderCoproductsOfShape J
  isStableUnderInfiniteComposition : W.IsStableUnderInfiniteComposition := by infer_instance

instance : (monomorphisms SSet.{u}).IsGabrielZismanSaturated := sorry

inductive gabrielZismanSaturation (W : MorphismProperty C) : MorphismProperty C
  | of_mem {X Y : C} (f : X ⟶ Y) (hf : W f) : gabrielZismanSaturation W f
  | of_isIso {X Y : C} (f : X ⟶ Y) (hf : IsIso f) : gabrielZismanSaturation W f
  | of_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : gabrielZismanSaturation W f)
      (hg : gabrielZismanSaturation W g) : gabrielZismanSaturation W (f ≫ g)
  | of_isPushout {A A' B B' : C} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
      (h : IsPushout g f f' g')
      (hf : gabrielZismanSaturation W f) : gabrielZismanSaturation W f'
  | of_retract {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'} (h : RetractArrow f f')
      (hf' : gabrielZismanSaturation W f') : gabrielZismanSaturation W f
  | of_infinite_composition (X : ℕ ⥤ C)
      (hX : ∀ (n : ℕ), gabrielZismanSaturation W (X.map (homOfLE (Nat.le_add_right n 1))))
      (c : Cocone X) (hc : IsColimit c) : gabrielZismanSaturation W (c.ι.app 0)
  | of_coproduct {J : Type w} (X₁ X₂ : Discrete J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f : X₁ ⟶ X₂)
      (_ : ∀ j, gabrielZismanSaturation W (f.app ⟨j⟩)) :
      gabrielZismanSaturation W (h₁.desc (Cocone.mk _ (f ≫ c₂.ι)))

section

variable (W : MorphismProperty C)

lemma le_gabrielZismanSaturation : W ≤ gabrielZismanSaturation.{w} W :=
  fun _ _ _ hf ↦ .of_mem _ hf

instance : W.gabrielZismanSaturation.IsMultiplicative where
  id_mem _ := .of_isIso _ inferInstance
  comp_mem f g hf hg := .of_comp f g hf hg

instance : W.gabrielZismanSaturation.IsStableUnderCobaseChange where
  of_isPushout sq := .of_isPushout sq

instance : W.gabrielZismanSaturation.IsStableUnderRetracts where
  of_retract h h' := .of_retract h h'

lemma gabrielZismanSaturation_isStableUnderCoproductsOfShape (J : Type w) :
    (gabrielZismanSaturation.{w} W).IsStableUnderCoproductsOfShape J := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f h
  exact .of_coproduct _ _ c₁ c₂ hc₁ hc₂ f (fun j ↦ h ⟨j⟩)

instance : IsGabrielZismanSaturated.{w} (gabrielZismanSaturation.{w} W) where
  isStableUnderCoproductsOfShape J X₁ X₂ c₁ c₂ hc₁ hc₂ f h :=
    gabrielZismanSaturation.of_coproduct.{w} _ _ _ _ hc₁ hc₂ f (fun j ↦ h ⟨j⟩)
  isStableUnderInfiniteComposition := ⟨by
    intro X Y f ⟨F, hF, c, hc⟩
    refine gabrielZismanSaturation.of_infinite_composition _
      (fun n ↦ hF _ (by simp)) _ hc⟩

end

end MorphismProperty

end CategoryTheory

namespace SSet

namespace AnodyneExtensions

def B₁ : MorphismProperty SSet.{u} :=
  ⨆ n, .ofHoms (fun i ↦ (subcomplexHorn.{u} n i).ι)

def B₂ : MorphismProperty SSet.{u} :=
  ⨆ (i : Fin 2), .ofHoms (fun (n : ℕ) ↦
    (Subcomplex.unionProd (standardSimplex.face {i}) (subcomplexBoundary n)).ι)

def B₃ : MorphismProperty SSet.{u} :=
  ⨆ (i : Fin 2), ⨆ (X : SSet.{u}),
    .ofHoms (fun (Y : X.Subcomplex) ↦ (Subcomplex.unionProd (standardSimplex.face {i}) Y).ι)

end AnodyneExtensions
