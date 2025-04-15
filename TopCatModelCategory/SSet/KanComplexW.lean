import TopCatModelCategory.SSet.FundamentalGroupoidAction

universe u

open CategoryTheory HomotopicalAlgebra Simplicial SSet.modelCategoryQuillen Simplicial

namespace SSet

namespace KanComplex

def W : MorphismProperty SSet.{u} := fun X Y f ↦
  ∃ (_ : IsFibrant X) (_ : IsFibrant Y),
    (mapFundamentalGroupoid f).IsEquivalence ∧
      ∀ (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y),
        Function.Bijective (mapπ f n x y h)

variable {X Y : SSet.{u}} (f : X ⟶ Y)

lemma W.mk [IsFibrant X] [IsFibrant Y] (h₀₁ : (mapFundamentalGroupoid f).IsEquivalence)
    (h : ∀ (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y),
      Function.Bijective (mapπ f n x y h)) : W f :=
  ⟨inferInstance, inferInstance, h₀₁, h⟩

variable {f}

lemma W.isFibrant_src (hf : W f) : IsFibrant X := hf.choose

lemma W.isFibrant_tgt (hf : W f) : IsFibrant Y := hf.choose_spec.choose

lemma W.isEquivalence [IsFibrant X] [IsFibrant Y] (hf : W f) :
    (mapFundamentalGroupoid f).IsEquivalence :=
  hf.choose_spec.choose_spec.1

lemma W.bijective (hf : W f) (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y) :
    Function.Bijective (mapπ f n x y h) :=
  hf.choose_spec.choose_spec.2 n x y h

lemma W.bijective_of_iso {n : ℕ} [IsFibrant X] [IsFibrant Y]
    {x y : FundamentalGroupoid X} (e : x ≅ y)
    (hx : Function.Bijective (mapπ f n x.pt _ rfl)) :
    Function.Bijective (mapπ f n y.pt _ rfl) := by
  rw [← isIso_iff_bijective] at hx ⊢
  exact (NatTrans.isIso_app_iff_of_iso
    (FundamentalGroupoid.actionMap f n) e).1 hx

variable (f) in
lemma W.of_iso [IsIso f] [IsFibrant X] [IsFibrant Y] : W f := by
  apply W.mk
  · infer_instance
  · intro n x y h
    exact (mapπEquivOfIso (asIso f) n x y h).bijective

variable (X) in
lemma W.id [IsFibrant X] : W (𝟙 X) := W.of_iso _

variable (f) {Z : SSet.{u}} (g : Y ⟶ Z)

lemma W.comp (hf : W f) (hg : W g) : W (f ≫ g) := by
  have := hf.isFibrant_src
  have := hf.isFibrant_tgt
  have := hg.isFibrant_tgt
  apply W.mk
  · have := hf.isEquivalence
    have := hg.isEquivalence
    exact Functor.isEquivalence_of_iso
      (compMapFundamentalGroupoidIso f g).symm
  · rintro n x _ rfl
    dsimp
    rw [← mapπ_comp_mapπ f n x _ rfl g _ rfl]
    exact (hg.bijective n _ _ rfl).comp (hf.bijective n x _ rfl)

lemma W.of_postcomp (hg : W g) (hfg : W (f ≫ g)) : W f := by
  have := hg.isFibrant_src
  have := hg.isFibrant_tgt
  have := hfg.isFibrant_src
  apply W.mk
  · have := hg.isEquivalence
    have := hfg.isEquivalence
    have := Functor.isEquivalence_of_iso
      (compMapFundamentalGroupoidIso f g)
    exact Functor.isEquivalence_of_comp_right _
      (mapFundamentalGroupoid g)
  · rintro n x _ rfl
    rw [← Function.Bijective.of_comp_iff' (hg.bijective n (f.app _ x) _ rfl),
      mapπ_comp_mapπ f n x _ rfl g _ rfl]
    exact hfg.bijective n x _ rfl

lemma W.of_precomp (hf : W f) (hfg : W (f ≫ g)) : W g := by
  have := hf.isFibrant_src
  have := hf.isFibrant_tgt
  have := hfg.isFibrant_tgt
  apply W.mk
  · have := hf.isEquivalence
    have := hfg.isEquivalence
    have := Functor.isEquivalence_of_iso
      (compMapFundamentalGroupoidIso f g)
    exact Functor.isEquivalence_of_comp_left
      (mapFundamentalGroupoid f) _
  · rintro n y _ rfl
    have hg (x : X _⦋0⦌) : Function.Bijective (mapπ g n (f.app _ x) _ rfl) := by
      rw [← Function.Bijective.of_comp_iff _ (hf.bijective n x _ rfl),
        mapπ_comp_mapπ f n x _ rfl g _ rfl]
      exact hfg.bijective n x _ rfl
    have := hf.isEquivalence
    exact W.bijective_of_iso
      (e := (mapFundamentalGroupoid f).objObjPreimageIso _) (hg _)

instance : W.{u}.HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := W.comp f g hf hg
  of_postcomp f g hg hfg := W.of_postcomp f g hg hfg
  of_precomp f g hf hfg := W.of_precomp f g hf hfg

lemma isFibrant_of_retract {X Y : SSet.{u}} (r : Retract X Y) [hY : IsFibrant Y] : IsFibrant X := by
  rw [isFibrant_iff, HomotopicalAlgebra.fibration_iff] at hY ⊢
  refine MorphismProperty.of_retract ?_ hY
  exact
    { i := Arrow.homMk r.i (𝟙 _)
      r := Arrow.homMk r.r (𝟙 _) }

attribute [local simp] mapπ_mapπ

@[simps]
def retractArrowMapπ {X X' Y Y' : SSet.{u}} {f : X ⟶ X'} {g : Y ⟶ Y'} (r : RetractArrow f g)
    (n : ℕ) (x : X _⦋0⦌) (x' : X' _⦋0⦌) (hxx' : f.app _ x = x')
    (y : Y _⦋0⦌) (y' : Y' _⦋0⦌) (hyy' : g.app _ y = y') (hy : r.left.i.app _ x = y) :
    RetractArrow (C := Type _) (mapπ f n x x' hxx') (mapπ g n y y' hyy') where
  i := Arrow.homMk (mapπ r.left.i n x y hy) ((mapπ r.right.i n x' y' (by
        subst hxx' hyy' hy
        exact congr_fun (congr_app r.i_w.symm _) x)))
  r := Arrow.homMk
      (mapπ r.left.r n y x (by
        subst hy
        exact congr_fun (congr_app r.left.retract _) x))
      (mapπ r.right.r n y' x' (by
        subst hxx' hyy' hy
        have : r.left.i ≫ g ≫ r.right.r = f := by simp
        exact congr_fun (congr_app this _) x))

open MorphismProperty

section

variable {X X' Y Y' : SSet.{u}} [IsFibrant X] [IsFibrant X'] [IsFibrant Y] [IsFibrant Y']
  {f : X ⟶ X'} {g : Y ⟶ Y'} (r : RetractArrow f g)

include r

lemma essSurj_mapFundamentalGroupoid_of_retract
    [(mapFundamentalGroupoid g).EssSurj] :
    (mapFundamentalGroupoid f).EssSurj where
  mem_essImage x' :=
    ⟨(mapFundamentalGroupoid r.left.r).obj
      ((mapFundamentalGroupoid g).objPreimage
      ((mapFundamentalGroupoid r.right.i).obj x')),
        ⟨((compMapFundamentalGroupoidIso' r.left.r f (g ≫ r.right.r) (by simp)).symm).app _ ≪≫
          (compMapFundamentalGroupoidIso g r.right.r).app _ ≪≫
          (mapFundamentalGroupoid r.right.r).mapIso
            (((mapFundamentalGroupoid g).objObjPreimageIso
            ((mapFundamentalGroupoid r.right.i).obj x'))) ≪≫
          (compMapFundamentalGroupoidIso' r.right.i r.right.r (𝟙 _) (by simp)).app _ ≪≫
          eqToIso (by
            apply FundamentalGroupoid.objEquiv.injective
            dsimp
            have := congr_app r.right.retract (Opposite.op ⦋0⦌)
            exact (congr_fun this _).trans (congr_fun this _))⟩⟩

noncomputable def retractArrowMapFundamentalGroupoidMap (x₀ x₁ : FundamentalGroupoid X) :
  RetractArrow (C := Type _)
    ((mapFundamentalGroupoid f).map (X := x₀) (Y := x₁))
    ((mapFundamentalGroupoid g).map (X := ((mapFundamentalGroupoid r.left.i).obj x₀))
      (Y := ((mapFundamentalGroupoid r.left.i).obj x₁))) := by
  have e₁ : mapFundamentalGroupoid f ⋙ mapFundamentalGroupoid r.right.i ≅
    mapFundamentalGroupoid r.left.i ⋙ mapFundamentalGroupoid g := by
      sorry
  have e₂ : mapFundamentalGroupoid r.left.r ⋙ mapFundamentalGroupoid f ≅
    mapFundamentalGroupoid g ⋙ mapFundamentalGroupoid r.right.r := by
      sorry
  have e₃ : mapFundamentalGroupoid r.left.i ⋙ mapFundamentalGroupoid r.left.r ≅ 𝟭 _ := by
    sorry
  let e₄ : mapFundamentalGroupoid r.left.i ⋙ mapFundamentalGroupoid g ⋙
      mapFundamentalGroupoid r.right.r ≅ mapFundamentalGroupoid f :=
    isoWhiskerLeft _ e₂.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight e₃ _ ≪≫ Functor.leftUnitor _
  exact {
    i := Arrow.homMk (fun p ↦ (mapFundamentalGroupoid r.left.i).map p)
      (fun q ↦ e₁.inv.app _ ≫ (mapFundamentalGroupoid r.right.i).map q ≫ e₁.hom.app _) (by
        ext p
        exact (NatIso.naturality_1 e₁ p).symm)
    r := Arrow.homMk
        (fun p ↦ e₃.inv.app _ ≫ (mapFundamentalGroupoid r.left.r).map p ≫ e₃.hom.app _)
        (fun q ↦ e₄.inv.app _ ≫ (mapFundamentalGroupoid r.right.r).map q ≫ e₄.hom.app _) (by
          ext p
          have := (NatIso.naturality_2 e₂ p).symm
          dsimp [e₄] at this p ⊢
          simp only [Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc, this])
    retract := by
      ext p
      · exact NatIso.naturality_1 e₃ p
      · dsimp [e₄] at p ⊢
        simp
        --have pif := NatIso.naturality_1 e₁ p
        sorry
      }

lemma faithful_mapFundamentalGroupoid_of_retract
    [(mapFundamentalGroupoid g).Faithful] :
    (mapFundamentalGroupoid f).Faithful where
  map_injective {x₀ x₁} := by
    rw [← mono_iff_injective]
    apply MorphismProperty.of_retract (P := monomorphisms _)
      (retractArrowMapFundamentalGroupoidMap r x₀ x₁)
    simp only [monomorphisms.iff]
    rw [mono_iff_injective]
    apply Functor.map_injective

lemma full_mapFundamentalGroupoid_of_retract
    [(mapFundamentalGroupoid g).Full] :
    (mapFundamentalGroupoid f).Full where
  map_surjective {x₀ x₁} := by
    rw [← epi_iff_surjective]
    apply MorphismProperty.of_retract (P := epimorphisms _)
      (retractArrowMapFundamentalGroupoidMap r x₀ x₁)
    simp only [epimorphisms.iff]
    rw [epi_iff_surjective]
    apply Functor.map_surjective

lemma isEquivalence_mapFundamentalGroupoid_of_retract
    [(mapFundamentalGroupoid g).IsEquivalence] :
    (mapFundamentalGroupoid f).IsEquivalence where
  full := full_mapFundamentalGroupoid_of_retract r
  faithful := faithful_mapFundamentalGroupoid_of_retract r
  essSurj := essSurj_mapFundamentalGroupoid_of_retract r

end

instance : W.{u}.IsStableUnderRetracts where
  of_retract {X X' Y Y' f g} r hg := by
    have := hg.isFibrant_src
    have := hg.isFibrant_tgt
    have := isFibrant_of_retract r.left
    have := isFibrant_of_retract r.right
    refine W.mk _ ?_ ?_
    · have := hg.isEquivalence
      exact isEquivalence_mapFundamentalGroupoid_of_retract r
    · intro n x x' h
      rw [← isIso_iff_bijective]
      apply of_retract (P := isomorphisms (Type u))
        (retractArrowMapπ r n x x' h _ _ rfl rfl)
      simp only [isomorphisms.iff]
      rw [isIso_iff_bijective]
      apply hg.bijective

end KanComplex

end SSet
