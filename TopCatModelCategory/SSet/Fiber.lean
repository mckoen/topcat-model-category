import TopCatModelCategory.SSet.Basic
import TopCatModelCategory.SSet.Subcomplex
import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.IsFibrant

universe u

open HomotopicalAlgebra CategoryTheory Limits Simplicial Opposite Category
  SSet.modelCategoryQuillen

namespace SSet

instance (n : SimplexCategoryᵒᵖ) : Subsingleton (Δ[0].obj n) where
  allEq f g := by
    obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective f
    obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective g
    obtain rfl : f = g := by
      ext i : 3
      dsimp
      apply Subsingleton.elim
    rfl

instance (n : SimplexCategoryᵒᵖ) : Unique (Δ[0].obj n) where
  default := stdSimplex.objEquiv.symm (SimplexCategory.const _ _ 0)
  uniq _ := Subsingleton.elim _ _

variable {X Y : SSet.{u}}

def isTerminal (F : SSet.{u}) [∀ (n : SimplexCategoryᵒᵖ), Unique (F.obj n)] :
    IsTerminal F :=
  IsTerminal.ofUniqueHom
    (fun X ↦ {
      app _ _ := default
      naturality _ _ _ := by ext; apply Subsingleton.elim _ _ })
    (fun X m ↦ by ext : 2; apply Subsingleton.elim)

def stdSimplex.objZeroIsTerminal :
    IsTerminal (Δ[0] : SSet.{u}) := isTerminal _

namespace Subcomplex

instance {n : SimplexCategoryᵒᵖ} (x : X _⦋0⦌) :
    Unique ((ofSimplex x).obj n) where
  default := ⟨X.map ((SimplexCategory.const _ _ 0).op) x, _, rfl⟩
  uniq := by
    rintro ⟨y, hy⟩
    simp only [mem_ofSimplex_obj_iff] at hy
    obtain ⟨f, rfl⟩ := hy
    obtain rfl := Subsingleton.elim f (SimplexCategory.const _ _ 0)
    rfl

instance {n : SimplexCategoryᵒᵖ} (x : X _⦋0⦌) :
    Unique ((ofSimplex x : SSet.{u}).obj n) :=
  inferInstanceAs (Unique ((ofSimplex x).obj n))

noncomputable def ofSimplexIsTerminal (x : X _⦋0⦌) :
    IsTerminal (ofSimplex x : SSet.{u}) :=
  isTerminal _

lemma ofSimplex_ι_app_zero (x : X _⦋0⦌) (y) :
    (ofSimplex x).ι.app (op ⦋0⦌) y = x := by
  rw [Subsingleton.elim y ⟨x, by exact mem_ofSimplex_obj x⟩, Subpresheaf.ι_app]

@[simp]
lemma ofSimplex_ι (x : X _⦋0⦌) : (ofSimplex x).ι = SSet.const x := by
  ext n ⟨_, ⟨u⟩, rfl⟩
  obtain rfl := Subsingleton.elim u (SimplexCategory.const _ _ 0)
  rfl

@[simp]
lemma ofSimplex_obj₀ (x : X _⦋0⦌) :
    (ofSimplex x).obj (op ⦋0⦌) = {x} := by
  ext y
  simp only [Set.mem_singleton_iff, mem_ofSimplex_obj_iff']
  constructor
  · rintro ⟨y, _, rfl⟩
    simp
  · rintro rfl
    exact ⟨yonedaEquiv (𝟙 _), by simp⟩

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

variable (f : X ⟶ Y) (y : Y _⦋0⦌)

def fiber : X.Subcomplex := (Subcomplex.ofSimplex y).preimage f

lemma mem_fiber_obj_zero_iff (x : X _⦋0⦌) :
    x ∈ (fiber f y).obj (op ⦋0⦌) ↔ f.app _ x = y := by
  simp [fiber]

@[simp]
lemma range_le_fiber_iff {Z : SSet.{u}} (g : Z ⟶ X) :
    Subcomplex.range g ≤ fiber f y ↔ g ≫ f = const y := by
  dsimp only [fiber]
  rw [← image_le_iff, le_ofSimplex_iff, ← range_comp,
    ← cancel_epi (toRangeSubcomplex (g ≫ f)),
    toRangeSubcomplex_ι, comp_const]

lemma le_fiber_iff (A : X.Subcomplex) :
    A ≤ fiber f y ↔ A.ι ≫ f = const y := by
  dsimp only [fiber]
  rw [← image_le_iff, le_ofSimplex_iff,
    ← cancel_epi (A.toImage f), comp_const, toImage_ι]

@[reassoc (attr := simp)]
lemma fiber_ι_comp : (fiber f y).ι ≫ f = const y := by
  rw [← le_fiber_iff]

instance isFibrant_fiber [Fibration f] : IsFibrant (C := SSet.{u}) (fiber f y) :=
  (isFibrant_iff_of_isTerminal (C := SSet.{u})
    ((Subcomplex.ofSimplex y).fromPreimage f) (isTerminal _)).2 inferInstance

lemma fiber_isPullback :
    IsPullback (fiber f y).ι (stdSimplex.objZeroIsTerminal.from _) f
      (yonedaEquiv.symm y) := by
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
