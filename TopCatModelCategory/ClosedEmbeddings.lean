import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition

universe u

open CategoryTheory Topology

namespace TopCat

def closedEmbeddings : MorphismProperty TopCat.{u} :=
  fun _ _ f ↦ IsClosedEmbedding f

lemma closedEmbeddings_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    closedEmbeddings f ↔ IsClosedEmbedding f := Iff.rfl

instance : closedEmbeddings.{u}.IsMultiplicative where
  id_mem _ := IsClosedEmbedding.id
  comp_mem _ _ hf hg := hg.comp hf

end TopCat
