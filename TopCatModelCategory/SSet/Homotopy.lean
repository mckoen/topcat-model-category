import TopCatModelCategory.IsFibrant
import TopCatModelCategory.SSet.AnodyneExtensions
import TopCatModelCategory.SSet.Horn

open HomotopicalAlgebra CategoryTheory Category Simplicial MonoidalCategory Opposite
  ChosenFiniteProducts Limits

universe u

namespace SSet

@[simps]
def const {X Y : SSet.{u}} (y : Y _[0]) : X ⟶ Y where
  app n _ := Y.map (n.unop.const _ 0).op y
  naturality n m f := by
    ext
    dsimp
    rw [← FunctorToTypes.map_comp_apply]
    rfl

@[reassoc (attr := simp)]
lemma const_comp {X Y Z : SSet.{u}} (y : Y _[0]) (g : Y ⟶ Z) :
    const (X := X) y ≫ g = const (g.app _ y) := by
  ext m x
  simp [FunctorToTypes.naturality]

private noncomputable abbrev ι₀ {X : SSet.{u}} : X ⟶ Δ[1] ⊗ X :=
  lift (const (standardSimplex.obj₀Equiv.{u}.symm 0)) (𝟙 X)

private noncomputable abbrev ι₁ {X : SSet.{u}} : X ⟶ Δ[1] ⊗ X :=
  lift (const (standardSimplex.obj₀Equiv.{u}.symm 1)) (𝟙 X)

namespace Subcomplex

variable {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) (φ : (A : SSet) ⟶ (B : SSet))

structure RelativeMorphism where
  map : X ⟶ Y
  comm : A.ι ≫ map = φ ≫ B.ι

namespace RelativeMorphism

attribute [reassoc (attr := simp)] comm

variable {A B φ} (f g : RelativeMorphism A B φ)

lemma map_eq_of_mem {n : SimplexCategoryᵒᵖ} (a : X.obj n) (ha : a ∈ A.obj n) :
    f.map.app n a = φ.app n ⟨a, ha⟩ :=
  congr_fun (congr_app f.comm n) ⟨a, ha⟩

@[simp]
lemma map_coe {n : SimplexCategoryᵒᵖ} (a : A.obj n) :
    f.map.app n a = φ.app n a := by
  apply map_eq_of_mem

lemma image_le : A.image f.map ≤ B := by
  rintro n _ ⟨a, ha, rfl⟩
  have := f.map_coe ⟨a, ha⟩
  aesop

lemma le_preimage : A ≤ B.preimage f.map := by
  simpa only [← image_le_iff] using f.image_le

structure Homotopy where
  h : Δ[1] ⊗ X ⟶ Y
  h₀ : ι₀ ≫ h = f.map := by aesop_cat
  h₁ : ι₁ ≫ h = g.map := by aesop_cat
  rel : _ ◁ A.ι ≫ h = snd _ _ ≫ φ ≫ B.ι := by aesop_cat

namespace Homotopy

@[simps]
noncomputable def refl : Homotopy f f where
  h := snd _ _ ≫ f.map

variable {f g}

-- consequence of the closed monoidal structure
instance (Y : SSet) : (tensorRight Y).IsLeftAdjoint := sorry

instance (J : Type*) [Category J] (Y : SimplexCategoryᵒᵖ ⥤ Type u) :
    PreservesColimitsOfShape J (tensorRight Y) :=
  inferInstanceAs (PreservesColimitsOfShape J (tensorRight (show SSet from Y)))

noncomputable def symm (hfg : Homotopy f g) [IsFibrant Y] : Homotopy g f := by
  apply Nonempty.some
  have := anodyneExtensions.subcomplex_unionProd_mem_of_left (subcomplexHorn 2 0) A
    (anodyneExtensions.subcomplexHorn_ι_mem 1 0)
  obtain ⟨α, hα₁, hα₂⟩ :=
    (subcomplexHorn₂₀.isPushout₀.{u}.map (tensorRight X)).exists_desc
      hfg.h (snd _ _ ≫ f.map) (by
        dsimp
        rw [whiskerRight_snd_assoc, ← hfg.h₀, SSet.ι₀,
          standardSimplex.obj₀Equiv_symm_apply, ← assoc]
        congr 1
        ext : 1
        · ext _ ⟨x, _⟩ _
          obtain ⟨x, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective x
          obtain rfl := Subsingleton.elim x (SimplexCategory.const _ _ 0)
          rfl
        · simp)
  dsimp at α hα₁ hα₂
  obtain ⟨β, hβ₁, hβ₂⟩ :=
    (unionProd.isPushout _ _).exists_desc (snd _ _ ≫ φ ≫ B.ι) α (by
      apply (subcomplexHorn₂₀.isPushout₀.{u}.map (tensorRight (A : SSet))).hom_ext
      · simp [← hfg.rel, ← hα₁, whisker_exchange_assoc]
      · dsimp
        simp [← whisker_exchange_assoc, hα₂,
          whiskerRight_snd_assoc, whiskerLeft_snd_assoc, comm])
  obtain ⟨h, fac⟩ := anodyneExtensions.exists_lift_of_isFibrant β
    (anodyneExtensions.subcomplex_unionProd_mem_of_left (subcomplexHorn 2 0) A
      (anodyneExtensions.subcomplexHorn_ι_mem 1 0))
  exact ⟨{
    h := standardSimplex.map (SimplexCategory.δ 0) ▷ _ ≫ h
    h₀ := by
      rw [← hfg.h₁, ← hα₁, ← hβ₂, ← fac, ← assoc, ← assoc, ← assoc, ← assoc]
      rfl
    h₁ := by simpa only [assoc, hβ₂, hα₂, lift_snd_assoc, id_comp,
        unionProd.ι₂_ι_assoc] using (SSet.ι₁ ≫ subcomplexHorn₂₀.ι₀₂ ▷ X ≫
          unionProd.ι₂ (subcomplexHorn 2 0) A) ≫= fac
    rel := by simpa only [assoc, hβ₁] using
        (standardSimplex.map (SimplexCategory.δ (0 : Fin 3)) ▷ _ ≫
          unionProd.ι₁ (subcomplexHorn 2 0) A) ≫= fac }⟩

noncomputable def trans {f₁ f₂ f₃ : RelativeMorphism A B φ}
    (h₁₂ : Homotopy f₁ f₂) (h₂₃ : Homotopy f₂ f₃) [IsFibrant Y] : Homotopy f₁ f₃ := by
  sorry

variable (A B φ) in
lemma equivalence [IsFibrant Y] :
    _root_.Equivalence (α := RelativeMorphism A B φ)
      (fun f g ↦ Nonempty (Homotopy f g)) where
  refl f := ⟨refl _⟩
  symm h := ⟨h.some.symm⟩
  trans h₁₂ h₂₃ := ⟨h₁₂.some.trans h₂₃.some⟩

end Homotopy

variable (A B φ)

def HomotopyClass : Type u :=
  Quot (α := RelativeMorphism A B φ) (fun f g ↦ Nonempty (Homotopy f g))

variable {A B φ}

def homotopyClass (f : RelativeMorphism A B φ) : HomotopyClass A B φ := Quot.mk _ f

lemma Homotopy.eq {f g : RelativeMorphism A B φ} (h : Homotopy f g) :
    f.homotopyClass = g.homotopyClass :=
  Quot.sound ⟨h⟩

lemma HomotopyClass.eq_homotopyClass (x : HomotopyClass A B φ) :
    ∃ (f : RelativeMorphism A B φ), f.homotopyClass = x :=
  Quot.mk_surjective x

noncomputable def Homotopy.of_eq {f g : RelativeMorphism A B φ} [IsFibrant Y]
    (h : f.homotopyClass = g.homotopyClass) : Homotopy f g :=
  ((Equivalence.quot_mk_eq_iff (Homotopy.equivalence A B φ) _ _).1 h).some

end RelativeMorphism

end Subcomplex

/-section

variable (X : SSet.{u})

def π₀ := Quot (α := X _[0]) (fun x y ↦ ∃ (p : X _[1]), X.δ 1 p = x ∧ X.δ 0 p = y)

def toπ₀ (x : X _[0]) : π₀ X := Quot.mk _ x

lemma toπ₀_surjective : Function.Surjective X.toπ₀ := by
  apply Quot.mk_surjective

lemma toπ₀_congr (p : X _[1]) : X.toπ₀ (X.δ 1 p) = X.toπ₀ (X.δ 0 p) :=
  Quot.sound ⟨p, rfl, rfl⟩

end-/

namespace KanComplex

variable (X : SSet.{u}) (n : ℕ) (x : X _[0])

def π : Type u :=
  Subcomplex.RelativeMorphism.HomotopyClass
    (subcomplexBoundary n) (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

end KanComplex

end SSet
