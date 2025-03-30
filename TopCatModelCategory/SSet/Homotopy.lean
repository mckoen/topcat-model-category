import TopCatModelCategory.SSet.FundamentalGroupoid
import TopCatModelCategory.SSet.Fibrations
import TopCatModelCategory.SSet.Fiber
import TopCatModelCategory.SSet.Monoidal
import TopCatModelCategory.SSet.HomotopyBasic
import TopCatModelCategory.IsFibrant
import TopCatModelCategory.SSet.AnodyneExtensions
import TopCatModelCategory.SSet.Horn

open HomotopicalAlgebra CategoryTheory Category Simplicial MonoidalCategory Opposite
  ChosenFiniteProducts Limits SSet.modelCategoryQuillen

namespace SSet

variable {X Y : SSet.{u}} {A : X.Subcomplex} {B : Y.Subcomplex} {φ : (A : SSet) ⟶ (B : SSet)}

namespace Subcomplex

variable (A B φ) in
noncomputable def relativeMorphism : ((ihom X).obj Y).Subcomplex :=
  Subcomplex.fiber ((MonoidalClosed.pre A.ι).app Y)
    (ihom₀Equiv.symm (φ ≫ B.ι))

instance [IsFibrant Y] :
    IsFibrant (C := SSet.{u}) (relativeMorphism A B φ) := by
  dsimp [relativeMorphism]
  infer_instance

namespace RelativeMorphism

@[simps]
noncomputable def equiv :
    RelativeMorphism A B φ ≃ (relativeMorphism A B φ : SSet.{u}) _⦋0⦌ where
  toFun f := ⟨ihom₀Equiv.symm f.map, by
    dsimp [relativeMorphism, fiber]
    rw [ofSimplex_obj₀, Set.mem_preimage, Set.mem_singleton_iff, ← f.comm,
      ihom₀Equiv_symm_comp]⟩
  invFun g :=
    { map := ihom₀Equiv g.1
      comm := by
        have := g.2
        simp [relativeMorphism, fiber] at this
        apply ihom₀Equiv.symm.injective
        rw [← this, ihom₀Equiv_symm_comp, Equiv.symm_apply_apply] }
  left_inv _ := by aesop
  right_inv _ := by aesop

namespace Homotopy

noncomputable def equiv {f g : RelativeMorphism A B φ} :
    Homotopy f g ≃ KanComplex.FundamentalGroupoid.Edge (X := relativeMorphism A B φ)
        (.mk (RelativeMorphism.equiv f))
        (.mk (RelativeMorphism.equiv g)) where
  toFun h := KanComplex.FundamentalGroupoid.Edge.mk
      (Subcomplex.lift (MonoidalClosed.curry h.h) sorry) (by
        rw [← cancel_mono (Subpresheaf.ι _), assoc, Subcomplex.lift_ι, const_comp,
          Subpresheaf.ι_app, equiv_apply_coe, ← h.h₀]
        apply yonedaEquiv.injective
        sorry) sorry
  invFun h :=
    { h := MonoidalClosed.uncurry (h.map ≫ Subpresheaf.ι _)
      h₀ := sorry
      h₁ := sorry
      rel := sorry }
  left_inv h := by aesop
  right_inv h := by aesop

noncomputable def symm {f g : RelativeMorphism A B φ}
    (hfg : Homotopy f g) [IsFibrant Y] : Homotopy g f := by
  apply Nonempty.some
  obtain ⟨h, _⟩ := KanComplex.FundamentalGroupoid.homMk_surjective
    (Groupoid.inv (KanComplex.FundamentalGroupoid.homMk (equiv hfg)))
  exact ⟨equiv.symm h⟩

noncomputable def trans {f₁ f₂ f₃ : RelativeMorphism A B φ}
    (h₁₂ : Homotopy f₁ f₂) (h₂₃ : Homotopy f₂ f₃) [IsFibrant Y] : Homotopy f₁ f₃ :=
  equiv.symm ((equiv h₁₂).comp (equiv h₂₃))

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
