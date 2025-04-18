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
  eq_iSup_coinduced : (TopCat.of A).str = ⨆ (i : ι),
    (TopCat.of (U i)).str.coinduced (fun ⟨x, hx⟩ ↦ ⟨x, toMulticoequalizerDiagram.le i hx⟩)

namespace MulticoequalizerDiagram

variable {A U V}

section

variable (h : MulticoequalizerDiagram A U V)

nonrec abbrev multispanIndex : MultispanIndex (.prod ι) TopCat.{u} :=
  h.multispanIndex.map Set.functorToTopCat

nonrec abbrev multicofork : Multicofork h.multispanIndex :=
  h.multicofork.map Set.functorToTopCat

lemma continuous_iff {B : Type*} [TopologicalSpace B] (f : A → B) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun (⟨x, hx⟩ : U i) ↦ f ⟨x, h.le i hx⟩) := by
  change Continuous[(TopCat.of A).str, _] f ↔ _
  rw [h.eq_iSup_coinduced, continuous_iSup_dom]
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

end

lemma mk_of_isOpen (h : CompleteLattice.MulticoequalizerDiagram A U V)
    (hU : ∀ i, IsOpen (U i)) :
    TopCat.MulticoequalizerDiagram A U V where
  toMulticoequalizerDiagram := h
  eq_iSup_coinduced := by
    ext W
    simp only [isOpen_iSup_iff, isOpen_coinduced]
    let f (i : ι) : U i → A := fun ⟨x, hx⟩ ↦ ⟨x, h.le i hx⟩
    have hf (i : ι) : Continuous (f i) := by continuity
    refine ⟨fun hF i ↦ IsOpen.preimage (hf i) hF, fun hF ↦ ?_⟩
    have hf' (i : ι) : IsOpenEmbedding (f i) :=
      { toIsEmbedding := IsEmbedding.inclusion (h.le i)
        isOpen_range := by
          rw [isOpen_induced_iff]
          aesop }
    have : W = ⋃ (i : ι), (f i) '' ((f i) ⁻¹' W) := by
      ext ⟨x, hx⟩
      rw [← h.iSup_eq] at hx
      aesop
    rw [this]
    exact isOpen_iUnion (fun i ↦ (hf' i).isOpenMap _ (hF i))

lemma mk_of_isClosed [Finite ι] (h : CompleteLattice.MulticoequalizerDiagram A U V)
    (hU : ∀ i, IsClosed (U i)) :
    TopCat.MulticoequalizerDiagram A U V where
  toMulticoequalizerDiagram := h
  eq_iSup_coinduced := by
    rw [TopologicalSpace.ext_iff_isClosed]
    intro F
    simp only [isClosed_iSup_iff, isClosed_coinduced]
    let f (i : ι) : U i → A := fun ⟨x, hx⟩ ↦ ⟨x, h.le i hx⟩
    have hf (i : ι) : Continuous (f i) := by continuity
    refine ⟨fun hF i ↦ IsClosed.preimage (hf i) hF, fun hF ↦ ?_⟩
    have hf' (i : ι) : IsClosedEmbedding (f i) :=
      { toIsEmbedding := IsEmbedding.inclusion (h.le i)
        isClosed_range := by
          rw [isClosed_induced_iff]
          aesop }
    have : F = ⋃ (i : ι), (f i) '' ((f i) ⁻¹' F) := by
      ext ⟨x, hx⟩
      rw [← h.iSup_eq] at hx
      aesop
    rw [this]
    exact isClosed_iUnion_of_finite (fun i ↦ (hf' i).isClosedMap _ (hF i))

end MulticoequalizerDiagram

end TopCat
