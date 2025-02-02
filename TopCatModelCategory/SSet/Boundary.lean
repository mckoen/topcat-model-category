import TopCatModelCategory.SSet.Subcomplex
import TopCatModelCategory.SSet.StandardSimplex
import TopCatModelCategory.SSet.HasDimensionLT

universe u

open CategoryTheory Simplicial Opposite

namespace SSet

lemma subcomplexBoundary_eq_iSup :
    subcomplexBoundary.{u} n = ⨆ (i : Fin (n + 1)), standardSimplex.face {i}ᶜ := by
  ext
  simp [standardSimplex.face, subcomplexBoundary, Function.Surjective]
  tauto

lemma face_le_subcomplexBoundary (i : Fin (n + 1)) :
    standardSimplex.face.{u} {i}ᶜ ≤ subcomplexBoundary n := by
  rw [subcomplexBoundary_eq_iSup]
  exact le_iSup (fun (i : Fin (n +1)) ↦ standardSimplex.face {i}ᶜ) i

lemma non_mem_subcomplexBoundary (n : ℕ):
    standardSimplex.objMk .id ∉ (subcomplexBoundary.{u} n).obj (op [n]) := by
  simp [subcomplexBoundary_eq_iSup]
  intro i hi
  simpa using @hi i (by aesop)

lemma subcomplexBoundary_obj_eq_top (m n : ℕ) (h : m < n) :
    (subcomplexBoundary.{u} n).obj (op [m]) = ⊤ := by
  ext x
  obtain ⟨f, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective x
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  obtain _ | n := n
  · simp at h
  · obtain ⟨i, q, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f (fun hf ↦ by
      rw [← SimplexCategory.epi_iff_surjective] at hf
      have := SimplexCategory.le_of_epi (f := f) inferInstance
      omega)
    apply face_le_subcomplexBoundary i
    simp
    intro i
    apply Fin.succAbove_ne

namespace standardSimplex

variable {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)

lemma subcomplex_hasDimensionLT_of_neq_top (h : A ≠ ⊤) :
    HasDimensionLT A n where
  degenerate_eq_top i hi := by
    ext ⟨a, ha⟩
    rw [A.mem_degenerate_iff]
    simp
    obtain hi | rfl := hi.lt_or_eq
    · simp [Δ[n].degenerate_eq_top_of_hasDimensionLT (n + 1) i (by omega)]
    · rw [mem_degenerate_iff_non_mem_nondegenerate, non_degenerate_top_dim]
      change a ∉ {objMk .id}
      rintro rfl
      apply h
      ext ⟨m⟩ x
      obtain ⟨f, rfl⟩ := (objEquiv _ _).symm.surjective x
      simpa using A.map f.op ha

lemma subcomplex_le_boundary_iff :
    A ≤ subcomplexBoundary n ↔ A ≠ ⊤ := by
  constructor
  · rintro h rfl
    exact non_mem_subcomplexBoundary.{u} n (h _ (by simp))
  · intro h
    have := subcomplex_hasDimensionLT_of_neq_top _ h
    rw [Subcomplex.le_iff_contains_nonDegenerate]
    rintro m ⟨x, h₁⟩ h₂
    dsimp at h₂ ⊢
    by_cases h₃ : m < n
    · simp [subcomplexBoundary_obj_eq_top m n (by simpa using h₃)]
    · simp only [not_lt] at h₃
      replace h₁ := (A.mem_non_degenerate_iff ⟨x, h₂⟩).2 h₁
      rw [nondegenerate_eq_bot_of_hasDimensionLT _ _ _ h₃] at h₁
      simp at h₁

instance : HasDimensionLT (subcomplexBoundary.{u} n) n := by
  apply subcomplex_hasDimensionLT_of_neq_top
  intro h
  simpa [h] using non_mem_subcomplexBoundary.{u} n

end standardSimplex

namespace subcomplexBoundary

def faceι (i : Fin (n + 1)) :
    (standardSimplex.face {i}ᶜ : SSet.{u}) ⟶ (subcomplexBoundary n : SSet.{u}) :=
  Subcomplex.homOfLE (face_le_subcomplexBoundary i)

@[reassoc (attr := simp)]
lemma faceι_ι (i : Fin (n + 2)) :
    faceι i ≫ (subcomplexBoundary.{u} (n + 1)).ι = (standardSimplex.face {i}ᶜ).ι := by
  simp [faceι]

def ι (i : Fin (n + 2)) :
    Δ[n] ⟶ subcomplexBoundary.{u} (n + 1) :=
  Subcomplex.lift ((standardSimplex.{u}.map (SimplexCategory.δ i)))
    (le_antisymm (by simp) (by
      rw [← Subcomplex.image_le_iff, Subcomplex.image_top,
        Subcomplex.range_eq_ofSimplex]
      refine le_trans ?_ (face_le_subcomplexBoundary i)
      rw [standardSimplex.face_singleton_compl]
      rfl))

@[reassoc (attr := simp)]
lemma ι_ι (i : Fin (n + 2)) :
    ι.{u} i ≫ (subcomplexBoundary.{u} (n + 1)).ι =
      standardSimplex.{u}.map (SimplexCategory.δ i) := rfl

@[reassoc (attr := simp)]
lemma faceSingletonComplIso_inv_ι (i : Fin (n + 2)) :
    (standardSimplex.faceSingletonComplIso i).inv ≫ ι i = subcomplexBoundary.faceι i := by
  rw [← cancel_epi (standardSimplex.faceSingletonComplIso i).hom, Iso.hom_inv_id_assoc]
  rfl

@[ext]
lemma hom_ext {n : ℕ} {X : SSet.{u}} {f g : (subcomplexBoundary (n + 1) : SSet) ⟶ X}
    (h : ∀ (i : Fin (n + 2)), ι i ≫ f = ι i ≫ g) :
    f = g := by
  ext m ⟨x, hx⟩
  simp [subcomplexBoundary_eq_iSup, standardSimplex.face_singleton_compl] at hx
  obtain ⟨i, ⟨y, rfl⟩⟩ := hx
  exact congr_fun ((congr_app (h i)) _) y

end subcomplexBoundary

end SSet
