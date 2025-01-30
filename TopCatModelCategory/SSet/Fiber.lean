import TopCatModelCategory.SSet.Basic
import TopCatModelCategory.SSet.Subcomplex
import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.IsFibrant

universe u

open HomotopicalAlgebra CategoryTheory Limits Simplicial Opposite Category

namespace SSet

instance (n : SimplexCategoryᵒᵖ) : Subsingleton (Δ[0].obj n) where
  allEq f g := by
    obtain ⟨f, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective f
    obtain ⟨g, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective g
    obtain rfl : f = g := by
      ext i : 3
      dsimp
      apply Subsingleton.elim
    rfl

instance (n : SimplexCategoryᵒᵖ) : Unique (Δ[0].obj n) where
  default := (standardSimplex.objEquiv  _ _ ).symm (SimplexCategory.const _ _ 0)
  uniq _ := Subsingleton.elim _ _

variable {X Y : SSet.{u}}

def isTerminal (F : SSet.{u}) [∀ (n : SimplexCategoryᵒᵖ), Unique (F.obj n)] :
    IsTerminal F :=
  IsTerminal.ofUniqueHom
    (fun X ↦ {
      app _ _ := default
      naturality _ _ _ := by ext; apply Subsingleton.elim _ _ })
    (fun X m ↦ by ext : 2; apply Subsingleton.elim)

def standardSimplex.objZeroIsTerminal :
    IsTerminal (Δ[0] : SSet.{u}) := isTerminal _

namespace Subcomplex

instance {n : SimplexCategoryᵒᵖ} (x : X _[0]) :
    Unique ((ofSimplex x).obj n) where
  default := ⟨X.map ((SimplexCategory.const _ _ 0).op) x, _, rfl⟩
  uniq := by
    rintro ⟨_, f, rfl⟩
    obtain ⟨f, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective f
    obtain rfl := Subsingleton.elim f (SimplexCategory.const _ _ 0)
    rfl

instance {n : SimplexCategoryᵒᵖ} (x : X _[0]) :
    Unique ((ofSimplex x : SSet.{u}).obj n) :=
  inferInstanceAs (Unique ((ofSimplex x).obj n))

noncomputable def ofSimplexIsTerminal (x : X _[0]) :
    IsTerminal (ofSimplex x : SSet.{u}) :=
  isTerminal _

lemma ofSimplex_ι_app_zero (x : X _[0]) (y) :
    (ofSimplex x).ι.app (op [0]) y = x := by
  rw [Subsingleton.elim y ⟨x, by exact mem_ofSimplex_obj x⟩, Subpresheaf.ι_app]

@[simp]
lemma ofSimplex_ι (x : X _[0]) : (ofSimplex x).ι = SSet.const x := by
  ext n ⟨_, u, rfl⟩
  simp

@[simp]
lemma ofSimplex_obj₀ (x : X _[0]) :
    (ofSimplex x).obj (op [0]) = {x} := by
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, _, rfl⟩
    simp
  · rintro rfl
    apply mem_ofSimplex_obj

lemma preimage_isPullback (B : Y.Subcomplex) (f : X ⟶ Y) :
    IsPullback (B.preimage f).ι (B.fromPreimage f) f B.ι where
  w := rfl
  isLimit' := ⟨PullbackCone.IsLimit.mk _
      (fun s ↦ Subcomplex.lift s.fst (by
        ext n x
        have := congr_fun (NatTrans.congr_app s.condition n) x
        dsimp at this
        simp [this]))
      (fun s ↦ rfl)
      (fun s ↦ by
        rw [← cancel_mono B.ι]
        exact s.condition)
      (fun s m h₁ h₂ ↦ by
        rw [← cancel_mono (B.preimage f).ι]
        exact h₁)⟩

instance (B : Y.Subcomplex) (f : X ⟶ Y) [hf : Fibration f] :
    Fibration (C := SSet.{u}) (B.fromPreimage f) := by
  rw [fibration_iff] at hf ⊢
  exact MorphismProperty.of_isPullback (C := SSet) (preimage_isPullback B f) hf

section

variable (f : X ⟶ Y) (y : Y _[0])

def fiber : X.Subcomplex := (Subcomplex.ofSimplex y).preimage f

instance [Fibration f] : IsFibrant (C := SSet.{u}) (fiber f y) :=
  (isFibrant_iff_of_isTerminal (C := SSet.{u})
    ((Subcomplex.ofSimplex y).fromPreimage f) (isTerminal _)).2 inferInstance

lemma fiber_isPullback :
    IsPullback (fiber f y).ι (standardSimplex.objZeroIsTerminal.from _) f
      ((yonedaEquiv _ _).symm y) := by
  let e : Subpresheaf.toPresheaf (Subcomplex.ofSimplex y) ≅ Δ[0] :=
    IsTerminal.uniqueUpToIso (isTerminal _) (isTerminal _)
  refine IsPullback.of_iso ((Subcomplex.ofSimplex y).preimage_isPullback f)
    (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by aesop)
    (by apply (isTerminal _).hom_ext) (by simp) ?_
  · dsimp
    rw [Subcomplex.ofSimplex_ι, comp_id, yonedaEquiv_symm_zero, comp_const]

end

end Subcomplex

end SSet
