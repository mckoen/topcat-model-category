import TopCatModelCategory.SSet.AnodyneExtensions
import TopCatModelCategory.SSet.Monoidal

universe u

open CategoryTheory MonoidalCategory HomotopicalAlgebra Limits MonoidalClosed

namespace CategoryTheory

namespace Arrow

variable {C : Type*} [Category C]

abbrev LiftStruct {f g : Arrow C} (φ : f ⟶ g) := (CommSq.mk φ.w).LiftStruct

lemma hasLiftingProperty_iff {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ ∀ (φ : Arrow.mk i ⟶ Arrow.mk p), Nonempty (LiftStruct φ) := by
  constructor
  · intro _ φ
    have sq : CommSq φ.left i p φ.right := (CommSq.mk φ.w)
    exact ⟨{ l := sq.lift }⟩
  · intro h
    exact ⟨fun {f g} sq ↦ ⟨h (Arrow.homMk f g sq.w)⟩⟩

end Arrow

namespace MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C]
  {A B X Y : C} [Closed A] [Closed B]

@[reassoc]
lemma whiskerRight_comp_uncurry (f : A ⟶ B) (g : X ⟶ (ihom B).obj Y) :
    f ▷ X ≫ uncurry g = uncurry (g ≫ (pre f).app Y) := by
  rw [uncurry_natural_left, uncurry_pre, whisker_exchange_assoc]
  rfl

@[reassoc]
lemma curry_whiskerRight_comp (f : A ⟶ B) (g : B ⊗ X ⟶ Y) :
    curry (f ▷ X ≫ g) = curry g ≫ (pre f).app Y := by
  apply uncurry_injective
  rw [uncurry_curry, ← whiskerRight_comp_uncurry, uncurry_curry]

end MonoidalClosed

end CategoryTheory

namespace SSet

variable {A B X Y : SSet.{u}}

section

variable {K L : SSet.{u}} (f : K ⟶ L) (i : A ⟶ B) (p : X ⟶ Y)

noncomputable abbrev fromPushoutProduct : pushout (i ▷ K) (A ◁ f) ⟶ B ⊗ L :=
  pushout.desc (B ◁ f) (i ▷ L) (by simp only [whisker_exchange])

variable {f i} in
noncomputable def fromPushoutProductCongr {K' L' A' B' : SSet.{u}} {f' : K' ⟶ L'}
    {i' : A' ⟶ B'}
    (e₁ : Arrow.mk f ≅ Arrow.mk f') (e₂ : Arrow.mk i ≅ Arrow.mk i') :
    Arrow.mk (fromPushoutProduct f i) ≅ Arrow.mk (fromPushoutProduct f' i') := by
  refine Arrow.isoMk
    { hom := pushout.map _ _ _ _ (e₂.hom.right ⊗ e₁.hom.left) (e₂.hom.left ⊗ e₁.hom.right)
        (e₂.hom.left ⊗ e₁.hom.left) ?_ ?_
      inv := pushout.map _ _ _ _ (e₂.inv.right ⊗ e₁.inv.left) (e₂.inv.left ⊗ e₁.inv.right)
        (e₂.inv.left ⊗ e₁.inv.left) ?_ ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
    (Arrow.rightFunc.mapIso e₂ ⊗ Arrow.rightFunc.mapIso e₁) ?_
  · have := e₂.hom.w
    dsimp at this
    simp only [tensorHom_def, Category.assoc, whisker_exchange, ← comp_whiskerRight_assoc, this]
  · have := e₁.hom.w
    dsimp at this
    simp only [tensorHom_def, Category.assoc, whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp, this]
  · have := e₂.inv.w
    dsimp at this
    simp only [tensorHom_def, Category.assoc, whisker_exchange, ← comp_whiskerRight_assoc, this]
  · have := e₁.inv.w
    dsimp at this
    simp only [tensorHom_def, Category.assoc, whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp, this]
  · simp [pushout.map_comp, ← tensor_comp]
  · simp [pushout.map_comp, ← tensor_comp]
  · dsimp only [Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Functor.id_map, Arrow.mk_hom,
      eq_mp_eq_cast, cast_eq, _root_.id_eq, eq_mpr_eq_cast, tensorIso_hom, Functor.mapIso_hom,
      Arrow.rightFunc_map]
    ext : 1
    · simp [tensorHom_def, whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp]
    · have := e₂.hom.w
      dsimp at this
      simp only [tensorHom_def, pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc,
        ← comp_whiskerRight_assoc, whisker_exchange, this]

noncomputable def fromPushoutProductιιIso' (A : K.Subcomplex) (B : L.Subcomplex) :
    Arrow.mk (fromPushoutProduct A.ι B.ι) ≅ Arrow.mk (B.unionProd A).ι :=
  Arrow.isoMk (Subcomplex.unionProd.isPushout B A).isoPushout.symm (Iso.refl _)

noncomputable def fromPushoutProductιιIso (A : K.Subcomplex) (B : L.Subcomplex) :
    Arrow.mk (fromPushoutProduct A.ι B.ι) ≅ Arrow.mk (A.unionProd B).ι :=
  fromPushoutProductιιIso' _ _ ≪≫
    Arrow.isoMk (Subcomplex.unionProd.symmIso _ _) (β_ _ _)

noncomputable abbrev ihomToPullback :
    (ihom B).obj X ⟶ pullback ((ihom A).map p) ((pre i).app Y) :=
  pullback.lift ((pre i).app X) ((ihom B).map p) (by simp)

variable {f i p} in
@[simps]
noncomputable def arrowMkFromPushoutProductHomEquiv :
    (Arrow.mk (fromPushoutProduct f i) ⟶ Arrow.mk p) ≃
      (Arrow.mk f ⟶ Arrow.mk (ihomToPullback i p)) where
  toFun φ :=
    Arrow.homMk (curry (pushout.inl _ _ ≫ φ.left))
      (pullback.lift (curry (pushout.inr _ _ ≫ φ.left)) (curry φ.right) (by
        have := φ.w
        dsimp at this
        rw [← curry_natural_right, Category.assoc, this, pushout.inr_desc_assoc,
          ← curry_whiskerRight_comp]
        dsimp)) (by
        dsimp
        ext : 1
        · dsimp
          simp only [Category.assoc, pullback.lift_fst,
            ← curry_whiskerRight_comp, ← curry_natural_left,
            pushout.condition_assoc]
        · dsimp
          have := φ.w
          dsimp at this
          simp only [Category.assoc, pullback.lift_snd, ← curry_natural_left,
            ← curry_natural_right, this, pushout.inl_desc_assoc])
  invFun ψ :=
    Arrow.homMk (pushout.desc (uncurry ψ.left) (uncurry (ψ.right ≫ pullback.fst _ _)) (by
        have := ψ.w =≫ pullback.fst _ _
        dsimp at this
        rw [Category.assoc, Category.assoc, pullback.lift_fst] at this
        rw [← uncurry_natural_left, ← this, whiskerRight_comp_uncurry]
        dsimp))
      (uncurry (ψ.right ≫ pullback.snd _ _)) (by
        dsimp only [Arrow.mk_left, Arrow.mk_hom]
        ext : 1
        · have := ψ.w =≫ pullback.snd _ _
          dsimp at this
          rw [Category.assoc, Category.assoc, pullback.lift_snd] at this
          rw [pushout.inl_desc_assoc, pushout.inl_desc_assoc,
            ← uncurry_natural_right, this, uncurry_natural_left]
        · rw [pushout.inr_desc_assoc, pushout.inr_desc_assoc,
            ← uncurry_natural_right, Category.assoc, pullback.condition,
            whiskerRight_comp_uncurry, Category.assoc]
          dsimp)
  left_inv φ := by
    ext : 1
    · dsimp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
        Arrow.homMk_left, Arrow.homMk_right]
      ext : 1
      · rw [pushout.inl_desc, uncurry_curry]
      · rw [pushout.inr_desc, pullback.lift_fst, uncurry_curry]
    · dsimp
      rw [pullback.lift_snd, uncurry_curry]
  right_inv ψ := by
    ext : 1
    · dsimp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
        Arrow.homMk_left, Arrow.homMk_right]
      rw [pushout.inl_desc, curry_uncurry]
    · dsimp only [Arrow.mk_right, Arrow.mk_left, Arrow.mk_hom,
        Arrow.homMk_left, Arrow.homMk_right]
      ext : 1
      · rw [pullback.lift_fst, pushout.inr_desc, curry_uncurry]
      · rw [pullback.lift_snd, curry_uncurry]

variable {f i p} in
noncomputable def fromPushoutProductLiftStructEquiv
    (φ : Arrow.mk (fromPushoutProduct f i) ⟶ Arrow.mk p) :
    Arrow.LiftStruct φ ≃
      Arrow.LiftStruct (arrowMkFromPushoutProductHomEquiv φ) where
  toFun l :=
    { l := curry l.l
      fac_left := by
        have := pushout.inl _ _ ≫= l.fac_left
        dsimp at this ⊢
        rw [← this, pushout.inl_desc_assoc, curry_natural_left]
      fac_right := by
        have h₁ := pushout.inr _ _ ≫= l.fac_left
        have h₂ := l.fac_right
        dsimp at h₁ h₂ ⊢
        ext : 1
        · simp only [Category.assoc, pullback.lift_fst, ← h₁, pushout.inr_desc_assoc,
            curry_whiskerRight_comp]
        · simp only [Category.assoc, pullback.lift_snd, ← h₂, curry_natural_right] }
  invFun l :=
    { l := uncurry l.l
      fac_left := by
        have h₁ := l.fac_left
        have h₂ := l.fac_right =≫ pullback.fst _ _
        dsimp at h₁ h₂ ⊢
        rw [pullback.lift_fst, Category.assoc, pullback.lift_fst] at h₂
        ext : 1
        · rw [pushout.inl_desc_assoc]
          apply curry_injective
          simp only [← h₁, curry_natural_left, curry_uncurry]
        · rw [pushout.inr_desc_assoc]
          apply curry_injective
          simp only [← h₂, curry_whiskerRight_comp, curry_uncurry]
      fac_right := by
        have := l.fac_right =≫ pullback.snd _ _
        dsimp at this ⊢
        rw [pullback.lift_snd, Category.assoc, pullback.lift_snd] at this
        apply curry_injective
        simp only [← this, ← uncurry_natural_right, curry_uncurry] }
  left_inv l := by ext : 1; apply uncurry_curry
  right_inv l := by ext : 1; apply curry_uncurry

lemma hasLiftingProperty_iHomToPullback_iff :
    HasLiftingProperty f (ihomToPullback i p) ↔
      HasLiftingProperty (fromPushoutProduct f i) p := by
  simp only [Arrow.hasLiftingProperty_iff]
  constructor
  · intro h φ
    exact ⟨(fromPushoutProductLiftStructEquiv _).symm (h _).some⟩
  · intro h ψ
    obtain ⟨φ, rfl⟩ := arrowMkFromPushoutProductHomEquiv.surjective ψ
    exact ⟨fromPushoutProductLiftStructEquiv _ ((h φ).some)⟩

end

section

instance (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] :
    Fibration (ihomToPullback i p) := by
  rw [ModelCategory.fibration_iff]
  intro _ _ _ hf
  simp only [ModelCategory.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨j⟩⟩ := hf
  rw [hasLiftingProperty_iHomToPullback_iff]
  apply anodyneExtensions.hasLeftLiftingProperty
  have : Mono i := by rwa [← ModelCategory.cofibration_iff]
  refine (anodyneExtensions.arrow_mk_iso_iff ?_).2
    (anodyneExtensions.subcomplex_unionProd_mem_of_left _ (Subcomplex.range i)
    (anodyneExtensions.subcomplexHorn_ι_mem _ j))
  exact fromPushoutProductCongr (Iso.refl _)
    (Arrow.isoMk (asIso (toRangeSubcomplex i)) (Iso.refl _) ) ≪≫ fromPushoutProductιιIso _ _

end

@[simps! hom_left inv_left hom_right]
noncomputable def ihomToPullbackTerminalFromArrowIso (f : A ⟶ B) (Z : SSet.{u}) :
    Arrow.mk (ihomToPullback f (terminal.from Z)) ≅
      Arrow.mk ((pre f).app Z) :=
  Arrow.isoMk (Iso.refl _)
    { hom := pullback.fst _ _
      inv := pullback.lift (𝟙 _) (by
        apply IsTerminal.from
        apply isLimitOfHasTerminalOfPreservesLimit) (by
          apply IsTerminal.hom_ext
          apply isLimitOfHasTerminalOfPreservesLimit)
      hom_inv_id := by
        dsimp
        ext : 1
        · simp
        · apply IsTerminal.hom_ext
          apply isLimitOfHasTerminalOfPreservesLimit
      inv_hom_id := by simp }

instance {Z : SSet.{u}} (f : A ⟶ B) [Cofibration f] [IsFibrant Z] :
    Fibration ((pre f).app Z) := by
  rw [fibration_iff]
  refine ((fibrations _).arrow_mk_iso_iff (ihomToPullbackTerminalFromArrowIso f Z)).1 ?_
  rw [← fibration_iff]
  infer_instance

@[simps! hom_left inv_left hom_right]
noncomputable def ihomToPullbackInitialToArrowIso
    (A : SSet.{u}) {X Y : SSet.{u}} (p : X ⟶ Y):
    Arrow.mk (ihomToPullback (initial.to A) p) ≅
      Arrow.mk ((ihom A).map p) :=
  Arrow.isoMk (Iso.refl _)
    { hom := pullback.snd _ _
      inv := pullback.lift (curry (by
        apply IsInitial.to
        apply isColimitOfHasInitialOfPreservesColimit (tensorRight _))) (𝟙 _) (by
          apply uncurry_injective
          apply IsInitial.hom_ext
          apply isColimitOfHasInitialOfPreservesColimit (tensorRight _))
      hom_inv_id := by
        dsimp
        ext : 1
        · apply uncurry_injective
          apply IsInitial.hom_ext
          apply isColimitOfHasInitialOfPreservesColimit (tensorRight _)
        · simp
      inv_hom_id := by simp }

open MorphismProperty in
instance (A : SSet.{u}) : Mono (initial.to A) := by
  have e : Arrow.mk (initial.to A) ≅ Arrow.mk (⊥ : A.Subcomplex).ι :=
    Arrow.isoMk (initialIsInitial.coconePointUniqueUpToIso
        (Subcomplex.isInitialBot A)) (Iso.refl _)
        (by dsimp; apply Subsingleton.elim)
  exact ((monomorphisms _).arrow_mk_iso_iff e).2
    (monomorphisms.infer_property _)

instance (p : X ⟶ Y) [Fibration p] :
    Fibration ((ihom A).map p) := by
  rw [fibration_iff]
  refine ((fibrations _).arrow_mk_iso_iff (ihomToPullbackInitialToArrowIso A p)).1 ?_
  rw [← fibration_iff]
  infer_instance

instance {A X : SSet.{u}} [IsFibrant X] : IsFibrant (A ⟶[SSet] X) := by
  rw [isFibrant_iff_of_isTerminal ((ihom A).map (terminal.from X))]
  · infer_instance
  · apply isLimitOfHasTerminalOfPreservesLimit

end SSet
