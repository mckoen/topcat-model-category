import TopCatModelCategory.SSet.Homotopy

open HomotopicalAlgebra CategoryTheory Simplicial
universe u

namespace SSet

namespace KanComplex

namespace π

variable {X : SSet.{u}} {x : X _[0]} {n : ℕ}

@[reassoc (attr := simp)]
lemma δ_map (s : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) (i : Fin (n + 2)) :
      standardSimplex.map (SimplexCategory.δ i) ≫ s.map = const x := by
  sorry

section

variable (i : Fin (n + 2))
  (φ : ({i}ᶜ : Set _) → Subcomplex.RelativeMorphism (subcomplexBoundary n) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩))

lemma exists_subcomplexHorn_desc :
    ∃ (f : Λ[(n + 1), i] ⟶ X), ∀ (j : ({i}ᶜ : Set _)),
      subcomplexHorn.faceι i j.1 j.2 ≫ f =
        (standardSimplex.faceSingletonComplIso j.1).inv ≫ (φ j).map := by
  sorry

end

structure CompStruct
    (g₁ g₂ g₁₂ : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩))
      (i : Fin (n + 1)) where
  map : Δ[n + 2] ⟶ X
  h₁ : standardSimplex.map (SimplexCategory.δ (i.succ.succ)) ≫ map = g₁₂.map
  h₂ : standardSimplex.map (SimplexCategory.δ (i.castSucc.castSucc)) ≫ map = g₁.map
  h_of_lt (j : Fin (n + 3)) (hj : j < i.castSucc.castSucc) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x
  h_of_gt (j : Fin (n + 3)) (hj : i.succ.succ < j) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x
  h₁₂ : standardSimplex.map (SimplexCategory.δ (i.castSucc.succ)) ≫ map = g₁₂.map

namespace CompStruct

def idComp (g : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) (i : Fin (n + 1)) :
      CompStruct .const g g i where
  map := standardSimplex.map (SimplexCategory.σ i.succ) ≫ g.map
  h₁ := by
    rw [← Functor.map_comp_assoc, SimplexCategory.δ_comp_σ_succ,
      CategoryTheory.Functor.map_id, Category.id_comp]
  h₂ := by
    simp [← Functor.map_comp_assoc,
      SimplexCategory.δ_comp_σ_of_le (i := i.castSucc) (j := i) (by rfl)]
  h_of_lt j hj := by
    have hj' : j ≠ Fin.last _ := by
      rintro rfl
      rw [Fin.lt_iff_val_lt_val, Fin.val_last, Fin.coe_castSucc] at hj
      omega
    have := SimplexCategory.δ_comp_σ_of_le (i := j.castPred hj') (j := i) hj.le
    rw [Fin.castSucc_castPred] at this
    simp [← Functor.map_comp_assoc, this]
  h_of_gt j hj := by
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by rintro rfl; simp at hj)
    rw [← Functor.map_comp_assoc]
    sorry
  h₁₂ := by
    rw [← Functor.map_comp_assoc, Fin.succ_castSucc, SimplexCategory.δ_comp_σ_self,
      CategoryTheory.Functor.map_id, Category.id_comp]

def compId (g : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) (i : Fin (n + 1)) :
      CompStruct g .const g i := sorry

end CompStruct

lemma exists_compStruct (g₁ g₂ : Subcomplex.RelativeMorphism (subcomplexBoundary (n + 1)) _
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩))
      (i : Fin (n + 1)) :
      ∃ g₁₂, Nonempty (CompStruct g₁ g₂ g₁₂ i) := sorry


end π
end KanComplex

end SSet
