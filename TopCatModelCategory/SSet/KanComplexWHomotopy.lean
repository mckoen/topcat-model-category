import TopCatModelCategory.SSet.KanComplexW
import TopCatModelCategory.SSet.Homotopy

universe u

open CategoryTheory HomotopicalAlgebra Simplicial SSet.modelCategoryQuillen
  ChosenFiniteProducts MonoidalCategory

namespace SSet

variable {X Y : SSet.{u}}


variable (X Y) in
structure HomotopyEquiv where
  hom : X ⟶ Y
  inv : Y ⟶ X
  homInvId : Homotopy (hom ≫ inv) (𝟙 X)
  invHomId : Homotopy (inv ≫ hom) (𝟙 Y)

variable (X) in
@[simps hom inv]
noncomputable def HomotopyEquiv.refl : HomotopyEquiv X X where
  hom := 𝟙 _
  inv := 𝟙 _
  homInvId := Subcomplex.RelativeMorphism.Homotopy.ofEq (by simp)
  invHomId := Subcomplex.RelativeMorphism.Homotopy.ofEq (by simp)

@[simps]
def HomotopyEquiv.symm (e : HomotopyEquiv X Y) : HomotopyEquiv Y X where
  hom := e.inv
  inv := e.hom
  homInvId := e.invHomId
  invHomId := e.homInvId

namespace KanComplex

variable [IsFibrant Y]
  {f₀ f₁ : X ⟶ Y} (h : Homotopy f₀ f₁) (n : ℕ)
  (x : X _⦋0⦌) {y₀ y₁ : Y _⦋0⦌} (hy₀ : f₀.app _ x = y₀) (hy₁ : f₁.app _ x = y₁)

@[simps! map]
noncomputable def edgeOfHomotopy : FundamentalGroupoid.Edge { pt := y₀ } { pt := y₁ } :=
  FundamentalGroupoid.Edge.mk (lift (const x) (𝟙 _) ≫ h.h) (by
    convert yonedaEquiv.symm x ≫= h.h₀ using 1
    · rw [← ι₀_comp_assoc, ι₀_stdSimplex_zero]
      rfl
    · simp [← hy₀]) (by
    convert yonedaEquiv.symm x ≫= h.h₁ using 1
    · rw [← ι₁_comp_assoc, ι₁_stdSimplex_zero]
      rfl
    · simp [← hy₁])

lemma congr_mapπ_of_homotopy :
    (FundamentalGroupoid.action.map (FundamentalGroupoid.homMk
      (edgeOfHomotopy h x hy₀ hy₁))).comp (mapπ f₀ n x y₀ hy₀) = mapπ f₁ n x y₁ hy₁ := by
  ext s
  obtain ⟨s, rfl⟩ := s.mk_surjective
  simp only [mapπ_mk, Function.comp_apply]
  exact FundamentalGroupoid.action.map_eq
    { map := s.map ▷ _ ≫ h.h
      whiskerRight_ι_comp_map := by
        simp only [edgeOfHomotopy_map, ← comp_whiskerRight_assoc, s.comm,
          Subcomplex.ofSimplex_ι, comp_const]
        rfl }

include h in
lemma bijective_mapπ_iff_of_homotopy [IsFibrant X] :
    Function.Bijective (mapπ f₀ n x y₀ hy₀) ↔
      Function.Bijective (mapπ f₁ n x y₁ hy₁) := by
  rw [← congr_mapπ_of_homotopy h n x hy₀ hy₁]
  symm
  apply Function.Bijective.of_comp_iff'
  apply FundamentalGroupoid.action.bijective_map

variable [IsFibrant X]

lemma isEquivalence_mapFundamentalGroupoid_homotopyEquivHom (e : HomotopyEquiv X Y) :
    (mapFundamentalGroupoid e.hom).IsEquivalence := sorry

lemma isEquivalence_mapFundamentalGroupoid_homotopyEquivInv (e : HomotopyEquiv X Y) :
    (mapFundamentalGroupoid e.inv).IsEquivalence :=
  isEquivalence_mapFundamentalGroupoid_homotopyEquivHom e.symm

lemma W.homotopyEquiv_hom (e : HomotopyEquiv X Y) :
    W e.hom := by
  have := isEquivalence_mapFundamentalGroupoid_homotopyEquivHom e
  refine W.mk _ inferInstance (fun n x y h ↦ ?_)
  subst h
  wlog hx : ∃ y, e.inv.app _ y = x generalizing x
  · exact W.bijective_of_iso (asIso (FundamentalGroupoid.homMk
      (edgeOfHomotopy e.homInvId x rfl rfl))) (this _ ⟨e.hom.app _ x, rfl⟩)
  constructor
  · have := (bijective_mapπ_iff_of_homotopy e.homInvId n x (y₁ := x) rfl rfl).2
      (by convert Function.bijective_id; aesop)
    rw [← mapπ_comp_mapπ _ _ _ _ rfl _ _ (by aesop)] at this
    exact this.1.of_comp
  · obtain ⟨y, hy⟩ := hx
    have := (bijective_mapπ_iff_of_homotopy e.invHomId n y (y₁ := y) rfl rfl).2
      (by convert Function.bijective_id; aesop)
    subst hy
    rw [← mapπ_comp_mapπ _ _ _ _ rfl _ _ (by aesop)] at this
    exact this.2.of_comp

lemma W.homotopyEquiv_inv (e : HomotopyEquiv X Y) :
    W e.inv := W.homotopyEquiv_hom e.symm

end KanComplex

end SSet
