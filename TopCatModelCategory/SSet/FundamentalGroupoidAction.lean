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
  whiskerRight_ι_comp_map : (boundary n).ι ▷ Δ[1] ≫ map = snd _ _ ≫ p.map
  ι₀_map : ι₀ ≫ map = s.map := by aesop_cat
  ι₁_map : ι₁ ≫ map = t.map := by aesop_cat

namespace action

variable {X : SSet.{u}} [IsFibrant X] {x₀ x₁ : FundamentalGroupoid X} {n : ℕ}

lemma exists_actionStruct [IsFibrant X] (p : Edge x₀ x₁)
    (s : Subcomplex.RelativeMorphism (boundary n) _
      (const ⟨x₀.pt, Subcomplex.mem_ofSimplex_obj x₀.pt⟩)) :
    ∃ t, Nonempty (ActionStruct p s t) :=
  sorry

def unique_actionStruct {p p' : Edge x₀ x₁} (hp : p.Homotopy p')
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

noncomputable def map : ∀ (_p : x₀ ⟶ x₁), π n X x₀.pt ⟶ π n X x₁.pt :=
  Quot.lift₂ (fun p s ↦ (map' p s).homotopyClass) (by
    rintro (p : Edge _ _) s s' ⟨hs⟩
    apply Subcomplex.RelativeMorphism.Homotopy.eq
    exact unique_actionStruct (.refl p) hs
      (actionStruct p s) (actionStruct p s')) (by
    rintro (p p' : Edge _ _) s ⟨hp⟩
    apply Subcomplex.RelativeMorphism.Homotopy.eq
    exact unique_actionStruct hp (.refl s)
      (actionStruct p s) (actionStruct p' s))

lemma map_eq {p : Edge x₀ x₁}
    {s : Subcomplex.RelativeMorphism (boundary n) _
      (const ⟨x₀.pt, Subcomplex.mem_ofSimplex_obj x₀.pt⟩)}
    {t : Subcomplex.RelativeMorphism (boundary n) _
        (const ⟨x₁.pt, Subcomplex.mem_ofSimplex_obj x₁.pt⟩)}
    (h : ActionStruct p s t) :
    map (FundamentalGroupoid.homMk p) s.homotopyClass = t.homotopyClass := by
  apply Subcomplex.RelativeMorphism.Homotopy.eq
  exact unique_actionStruct (.refl p) (.refl s) (actionStruct p s) h

end action

@[simps obj]
noncomputable def action (X : SSet.{u}) [IsFibrant X] (n : ℕ) :
    FundamentalGroupoid X ⥤ Type u where
  obj x := π n X x.pt
  map {x y} p := action.map p
  map_id := sorry
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
  naturality := sorry

end FundamentalGroupoid

end KanComplex

end SSet
