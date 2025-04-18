import Mathlib.Topology.Category.TopCat.Limits.Basic
import TopCatModelCategory.ColimitsType

universe w u

open CategoryTheory Topology Limits

namespace CompleteLattice.MulticoequalizerDiagram

variable {T : Type*} [CompleteLattice T] {ι : Type w} {A : T} {U : ι → T} {V : ι → ι → T}

lemma le (h : MulticoequalizerDiagram A U V) (i : ι) : U i ≤ A := by
  rw [← h.iSup_eq]
  exact le_iSup U i

end CompleteLattice.MulticoequalizerDiagram

namespace Set

variable {X : Type u} [TopologicalSpace X]

@[simps]
def functorToTopCat : Set X ⥤ TopCat.{u} where
  obj S := TopCat.of S
  map {S T} φ := TopCat.ofHom ⟨fun ⟨x, hx⟩ ↦ ⟨x, leOfHom φ hx⟩, by continuity⟩

end Set

namespace TopCat

variable {X : TopCat.{u}} {ι : Type w} (A : Set X) (U : ι → Set X) (V : ι → ι → Set X)

structure MulticoequalizerDiagram extends CompleteLattice.MulticoequalizerDiagram A U V where
  top_eq : (TopCat.of A).str = ⨆ (i : ι),
    (TopCat.of (U i)).str.coinduced (fun ⟨x, hx⟩ ↦ ⟨x, toMulticoequalizerDiagram.le i hx⟩)

namespace MulticoequalizerDiagram

variable {A U V} (h : MulticoequalizerDiagram A U V)

nonrec abbrev multispanIndex : MultispanIndex (.prod ι) TopCat.{u} :=
  h.multispanIndex.map Set.functorToTopCat

nonrec abbrev multicofork : Multicofork h.multispanIndex :=
  h.multicofork.map Set.functorToTopCat

lemma continuous_iff {B : Type*} [TopologicalSpace B] (f : A → B) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun (⟨x, hx⟩ : U i) ↦ f ⟨x, h.le i hx⟩) := by
  trans Continuous[(TopCat.of A).str, _] f
  · rfl
  · rw [h.top_eq, continuous_iSup_dom]
    simp only [continuous_coinduced_dom]
    rfl

noncomputable def multicoforkIsColimit : IsColimit h.multicofork :=
  Multicofork.IsColimit.mk _
    (fun s ↦ ofHom ⟨(Types.isColimitMulticoforkMapSetToTypes
        h.toMulticoequalizerDiagram).desc (Multicofork.map s (forget _)), by
        rw [h.continuous_iff]
        intro i
        convert (s.ι.app (.right i)).hom.continuous using 1
        dsimp
        exact (Types.isColimitMulticoforkMapSetToTypes
          h.toMulticoequalizerDiagram).fac (Multicofork.map s (forget _)) (.right i)⟩)
    (fun s j ↦ (forget _).map_injective
      (((Types.isColimitMulticoforkMapSetToTypes h.toMulticoequalizerDiagram).fac
        (Multicofork.map s (forget _)) (.right j))))
    (fun s m hm ↦ (forget _).map_injective
      (Multicofork.IsColimit.hom_ext
        ((Types.isColimitMulticoforkMapSetToTypes h.toMulticoequalizerDiagram)) (fun j ↦
          Eq.trans (by dsimp; rw [← hm]; rfl)
            ((Types.isColimitMulticoforkMapSetToTypes h.toMulticoequalizerDiagram).fac
              (Multicofork.map s (forget _)) (.right j)).symm)))

end MulticoequalizerDiagram

end TopCat
