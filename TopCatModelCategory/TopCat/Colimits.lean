import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

universe v' u' u

open CategoryTheory Limits Topology

namespace TopCat

variable {J : Type u'} [Category.{v'} J] {F : J ⥤ TopCat.{u}}
  (c : Cocone F)

lemma nonempty_isColimit_iff :
    Nonempty (IsColimit c) ↔
      Nonempty (IsColimit ((forget _).mapCocone c)) ∧
        c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app j) := by
  constructor
  · rintro ⟨hc⟩
    exact ⟨⟨isColimitOfPreserves _ hc⟩ , coinduced_of_isColimit _ hc⟩
  · rintro ⟨⟨hc⟩, hc'⟩
    exact ⟨IsColimit.ofIsoColimit (isColimitCoconeOfForget _ hc)
      (Cocones.ext (isoOfHomeo (Homeomorph.mk (.refl _) ⟨by aesop⟩
        ⟨by aesop⟩)) (by aesop))⟩

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃)
  (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄)

lemma isPushout_iff :
    IsPushout t l r b ↔
      IsPushout ((forget _).map t) ((forget _).map l)
        ((forget _).map r) ((forget _).map b) ∧
        X₄.str = X₂.str.coinduced r ⊔ X₃.str.coinduced b := by
  wlog H : CommSq t l r b
  · constructor
    · intro h
      rwa [this] at h
      exact ⟨h.w⟩
    · intro h
      rwa [this]
      exact ⟨(forget _).map_injective h.1.w⟩
  let c := (PushoutCocone.mk _ _ H.w)
  have : X₂.str.coinduced r ⊔ X₃.str.coinduced b =
      ⨆ j, ((span t l).obj j).str.coinduced (c.ι.app j) := by
    apply le_antisymm
    · rw [sup_le_iff]
      let φ (j) : TopologicalSpace c.pt := ((span t l).obj j).str.coinduced (c.ι.app j)
      exact ⟨le_iSup φ .left, le_iSup φ .right⟩
    · rw [iSup_le_iff]
      rintro (_ | _ | _)
      · refine le_trans ?_ le_sup_left
        dsimp [c]
        rw [← coinduced_compose]
        apply coinduced_mono
        apply Continuous.coinduced_le
        continuity
      · apply le_sup_left
      · apply le_sup_right
  rw [this]
  trans Nonempty (IsColimit c)
  · exact ⟨fun h ↦ ⟨h.isColimit⟩, fun ⟨h⟩ ↦ { w := H.w, isColimit' := ⟨h⟩ }⟩
  · rw [nonempty_isColimit_iff]
    refine and_congr_left (fun _ ↦ ⟨fun ⟨h⟩ ↦
      { w := (forget _).congr_map H.w
        isColimit' := ⟨PushoutCocone.isColimitMapCoconeEquiv _ _ h⟩ },
      fun h ↦ ⟨(PushoutCocone.isColimitMapCoconeEquiv _ _).2 h.isColimit⟩⟩)

end TopCat
