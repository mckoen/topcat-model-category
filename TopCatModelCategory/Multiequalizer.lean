import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Preserves.Basic

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

namespace Limits

@[simps]
def MultispanIndex.map (d : MultispanIndex C) (F : C ⥤ D) : MultispanIndex D where
  L := d.L
  R := d.R
  fstFrom := d.fstFrom
  sndFrom := d.sndFrom
  left i := F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

@[simps!]
def Multicofork.map {d : MultispanIndex C} (c : Multicofork d) (F : C ⥤ D) :
    Multicofork (d.map F) :=
  Multicofork.ofπ _ (F.obj c.pt) (fun i ↦ F.map (c.π i)) (fun j ↦ by
    dsimp
    rw [← F.map_comp, ← F.map_comp, condition])

@[simps!]
def MultispanIndex.multispanCompIso
    (d : MultispanIndex C) (F : C ⥤ D) :
    d.multispan ⋙ F ≅ (d.map F).multispan :=
  NatIso.ofComponents (fun X ↦ match X with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro _ _ (_ | _) <;> simp)

def Multicofork.ext {d : MultispanIndex C} {c c' : Multicofork d}
    (e : c.pt ≅ c'.pt) (h : ∀ (i : d.R), c.π i ≫ e.hom = c'.π i := by aesop_cat) : c ≅ c' :=
  Cocones.ext e (by rintro (i | j) <;> simp [h])

def isColimitMapMulticoforkEquiv {d : MultispanIndex C} (c : Multicofork d) (F : C ⥤ D) :
    IsColimit (F.mapCocone c) ≃ IsColimit (c.map F) :=
  (IsColimit.precomposeInvEquiv (d.multispanCompIso F) (F.mapCocone c)).symm.trans
    (IsColimit.equivIsoColimit
      (Multicofork.ext (Iso.refl _) (fun i ↦ by dsimp only [Multicofork.π]; simp)))

end Limits

end CategoryTheory
