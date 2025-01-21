import TopCatModelCategory.SSet.HomotopyBasic
import TopCatModelCategory.IsFibrant
import TopCatModelCategory.SSet.AnodyneExtensions
import TopCatModelCategory.SSet.Horn

open HomotopicalAlgebra CategoryTheory Category Simplicial MonoidalCategory Opposite
  ChosenFiniteProducts Limits

namespace SSet

variable {X Y : SSet.{u}} {A : X.Subcomplex} {B : Y.Subcomplex} {φ : (A : SSet) ⟶ (B : SSet)}

namespace Subcomplex

namespace RelativeMorphism

namespace Homotopy

-- consequence of the closed monoidal structure
instance (Y : SSet) : (tensorRight Y).IsLeftAdjoint := sorry

instance (J : Type*) [Category J] (Y : SimplexCategoryᵒᵖ ⥤ Type u) :
    PreservesColimitsOfShape J (tensorRight Y) :=
  inferInstanceAs (PreservesColimitsOfShape J (tensorRight (show SSet from Y)))

noncomputable def symm {f g : RelativeMorphism A B φ}
    (hfg : Homotopy f g) [IsFibrant Y] : Homotopy g f := by
  apply Nonempty.some
  obtain ⟨α, hα₁, hα₂⟩ :=
    (subcomplexHorn₂₀.isPushout.{u}.map (tensorRight X)).exists_desc
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
      apply (subcomplexHorn₂₀.isPushout.{u}.map (tensorRight (A : SSet))).hom_ext
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
  refl _ := ⟨refl _⟩
  symm h := ⟨h.some.symm⟩
  trans h₁₂ h₂₃ := ⟨h₁₂.some.trans h₂₃.some⟩

end Homotopy

noncomputable def Homotopy.of_eq {f g : RelativeMorphism A B φ} [IsFibrant Y]
    (h : f.homotopyClass = g.homotopyClass) : Homotopy f g :=
  ((Equivalence.quot_mk_eq_iff (Homotopy.equivalence A B φ) _ _).1 h).some

end RelativeMorphism

end Subcomplex

end SSet
