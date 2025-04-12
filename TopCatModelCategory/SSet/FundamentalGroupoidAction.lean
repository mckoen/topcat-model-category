import TopCatModelCategory.SSet.AnodyneExtensionsAdjunctions
import TopCatModelCategory.SSet.FundamentalGroupoid
import TopCatModelCategory.SSet.HomotopyGroup

universe u

open HomotopicalAlgebra CategoryTheory Simplicial MonoidalCategory ChosenFiniteProducts
  SSet.modelCategoryQuillen

namespace SSet

namespace KanComplex

namespace FundamentalGroupoid

structure ActionStruct {X : SSet.{u}} {x₀ x₁ : FundamentalGroupoid X} {n : ℕ}
    (p : Edge x₀ x₁)
    (s : Subcomplex.RelativeMorphism (boundary n) _
        (const ⟨x₀.pt, Subcomplex.mem_ofSimplex_obj x₀.pt⟩))
    (t : Subcomplex.RelativeMorphism (boundary n) _
        (const ⟨x₁.pt, Subcomplex.mem_ofSimplex_obj x₁.pt⟩)) where
  map : Δ[n] ⊗ Δ[1] ⟶ X
  whiskerRight_ι_comp_map : (boundary n).ι ▷ Δ[1] ≫ map = snd _ _ ≫ p.map := by aesop_cat
  ι₀_map : ι₀ ≫ map = s.map := by aesop_cat
  ι₁_map : ι₁ ≫ map = t.map := by aesop_cat

namespace ActionStruct

attribute [reassoc (attr := simp)] ι₀_map ι₁_map whiskerRight_ι_comp_map

noncomputable def pushforward {X Y : SSet.{u}} [IsFibrant X] {x₀ x₁ : FundamentalGroupoid X}
    {n : ℕ} {p : Edge x₀ x₁} {s : PtSimplex X n x₀.pt} {t : PtSimplex X n x₁.pt}
    (h : ActionStruct p s t) (f : X ⟶ Y) :
    ActionStruct (p.pushforward f) (s.pushforward f _ rfl)
      (t.pushforward f _ rfl) where
  map := h.map ≫ f

end ActionStruct

namespace action

variable {X : SSet.{u}} [IsFibrant X] {x₀ x₁ : FundamentalGroupoid X} {n : ℕ}

lemma exists_actionStruct (p : Edge x₀ x₁)
    (s : Subcomplex.RelativeMorphism (boundary n) _
      (const ⟨x₀.pt, Subcomplex.mem_ofSimplex_obj x₀.pt⟩)) :
    ∃ t, Nonempty (ActionStruct p s t) := by
  obtain ⟨φ, hφ₁, hφ₂⟩ :=
    (Subcomplex.unionProd.isPushout ∂Δ[n] (stdSimplex.face {(0 : Fin 2)})).exists_desc
      (fst _ _ ≫ s.map) (snd _ _ ≫ p.map) (by
        rw [whiskerRight_fst_assoc, s.comm, Subcomplex.ofSimplex_ι, comp_const, comp_const,
          whiskerLeft_snd_assoc, p.comm₀'', comp_const])
  obtain ⟨l, hl⟩ := anodyneExtensions.exists_lift_of_isFibrant φ
    (anodyneExtensions.subcomplex_unionProd_mem_of_right.{u} ∂Δ[n] _
    (anodyneExtensions.face 0))
  refine ⟨{
    map := ι₁ ≫ l
    comm := by
      have := Subcomplex.unionProd.ι₂ _ _ ≫= hl
      rw [Subcomplex.unionProd.ι₂_ι_assoc, hφ₂] at this
      rw [Subcomplex.ofSimplex_ι, comp_const, ← ι₁_comp_assoc, this,
        ι₁_snd_assoc, const_comp, p.comm₁']
  }, ⟨{
      map := l
      ι₀_map := by
        have := Subcomplex.unionProd.ι₁ _ _ ≫= hl
        rw [hφ₁, ← cancel_epi (Δ[n] ◁ (stdSimplex.faceSingletonIso.{u} (0 : Fin 2)).hom),
          ← cancel_epi (stdSimplex.rightUnitor _).inv] at this
        exact this
      ι₁_map := rfl
      whiskerRight_ι_comp_map := by rw [← hφ₂, ← hl]; rfl
  }⟩⟩

def uniqueActionStruct {p p' : Edge x₀ x₁} (hp : p.Homotopy p')
    {s s' : Subcomplex.RelativeMorphism (boundary n) _
      (const ⟨x₀.pt, Subcomplex.mem_ofSimplex_obj x₀.pt⟩)} (hs : s.Homotopy s')
    {t t' : Subcomplex.RelativeMorphism (boundary n) _
      (const ⟨x₁.pt, Subcomplex.mem_ofSimplex_obj x₁.pt⟩)}
    (ht : ActionStruct p s t) (ht' : ActionStruct p' s' t') :
    t.Homotopy t' := by
  sorry

noncomputable def map' (p : Edge x₀ x₁)
    (s : Subcomplex.RelativeMorphism (boundary n) _
        (const ⟨x₀.pt, Subcomplex.mem_ofSimplex_obj x₀.pt⟩)) :
    Subcomplex.RelativeMorphism (boundary n) _
        (const ⟨x₁.pt, Subcomplex.mem_ofSimplex_obj x₁.pt⟩) :=
  (exists_actionStruct p s).choose

noncomputable def actionStruct (p : Edge x₀ x₁)
    (s : Subcomplex.RelativeMorphism (boundary n) _
        (const ⟨x₀.pt, Subcomplex.mem_ofSimplex_obj x₀.pt⟩)) :
    ActionStruct p s (map' p s) :=
  (exists_actionStruct p s).choose_spec.some

noncomputable def map : ∀ (_p : x₀ ⟶ x₁), π n X x₀.pt → π n X x₁.pt :=
  Quot.lift₂ (fun p s ↦ (map' p s).homotopyClass) (by
    rintro (p : Edge _ _) s s' ⟨hs⟩
    apply Subcomplex.RelativeMorphism.Homotopy.eq
    exact uniqueActionStruct (.refl p) hs
      (actionStruct p s) (actionStruct p s')) (by
    rintro (p p' : Edge _ _) s ⟨hp⟩
    apply Subcomplex.RelativeMorphism.Homotopy.eq
    exact uniqueActionStruct hp (.refl s)
      (actionStruct p s) (actionStruct p' s))

lemma map_eq {p : Edge x₀ x₁}
    {s : Subcomplex.RelativeMorphism (boundary n) _
      (const ⟨x₀.pt, Subcomplex.mem_ofSimplex_obj x₀.pt⟩)}
    {t : Subcomplex.RelativeMorphism (boundary n) _
        (const ⟨x₁.pt, Subcomplex.mem_ofSimplex_obj x₁.pt⟩)}
    (h : ActionStruct p s t) :
    map (FundamentalGroupoid.homMk p) s.homotopyClass = t.homotopyClass := by
  apply Subcomplex.RelativeMorphism.Homotopy.eq
  exact uniqueActionStruct (.refl p) (.refl s) (actionStruct p s) h

variable (n) in
@[simp]
lemma map_id (x : FundamentalGroupoid X) :
    action.map (n := n) (𝟙 x) = id := by
  ext s
  obtain ⟨s, rfl⟩ := s.mk_surjective
  exact map_eq { map := fst _ _ ≫ s.map }

end action

@[simps]
noncomputable def action (X : SSet.{u}) [IsFibrant X] (n : ℕ) :
    FundamentalGroupoid X ⥤ Type u where
  obj x := π n X x.pt
  map {x y} p := action.map p
  map_comp := sorry

lemma action.bijective_map (n : ℕ) {X : SSet.{u}} {x y : FundamentalGroupoid X} [IsFibrant X]
    (p : x ⟶ y) :
    Function.Bijective (action.map (n := n) p) := by
  rw [← isIso_iff_bijective]
  exact inferInstanceAs (IsIso ((action X n).map p))

@[simps]
def actionMap {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) (n : ℕ) :
    action X n ⟶ mapFundamentalGroupoid f ⋙ action Y n where
  app x := mapπ f n x.pt _ rfl
  naturality x y p := by
    ext s
    obtain ⟨s, rfl⟩ := s.mk_surjective
    obtain ⟨p, rfl⟩ := FundamentalGroupoid.homMk_surjective p
    have h := action.actionStruct p s
    dsimp
    erw [action.map_eq h, mapπ_mk, action.map_eq (h.pushforward f)]
    rfl

end FundamentalGroupoid

end KanComplex

end SSet
