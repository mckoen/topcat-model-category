import TopCatModelCategory.SSet.NonDegenerateProdSimplex

universe u

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace SSet

variable {X₁ X₂ : SSet.{u}}

noncomputable def Subcomplex.ofSimplexProd {p q : ℕ} (x₁ : X₁ _[p]) (x₂ : X₂ _[q]) :
    (X₁ ⊗ X₂).Subcomplex :=
  (Subcomplex.ofSimplex x₁).prod (Subcomplex.ofSimplex x₂)

lemma Subcomplex.range_prod {X₁ X₂ Y₁ Y₂ : SSet.{u}} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) : range (f₁ ⊗ f₂) = (range f₁).prod (range f₂) := by
  ext m ⟨y₁, y₂⟩
  constructor
  · rintro ⟨⟨x₁, x₂⟩, h⟩
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    exact ⟨⟨x₁, h.1⟩, ⟨x₂, h.2⟩⟩
  · rintro ⟨⟨x₁, rfl⟩, ⟨x₂, rfl⟩⟩
    exact ⟨⟨x₁, x₂⟩, rfl⟩

lemma Subcomplex.ofSimplexProd_eq_range {p q : ℕ} (x₁ : X₁ _[p]) (x₂ : X₂ _[q]) :
    (Subcomplex.ofSimplexProd x₁ x₂) =
      Subcomplex.range ((yonedaEquiv _ _).symm x₁ ⊗ (yonedaEquiv _ _).symm x₂) := by
  simp only [ofSimplexProd, ofSimplex, Subcomplex.range_prod]

instance {p q : ℕ} (x₁ : X₁ _[p]) (x₂ : X₂ _[q]) :
    HasDimensionLT (Subcomplex.ofSimplexProd x₁ x₂) (p + q + 1) := by
  rw [Subcomplex.ofSimplexProd_eq_range]
  infer_instance

variable (X₁ X₂)

lemma subcomplex_prod_eq_top :
    ⨆ (x₁ : Σ (p : ℕ), X₁.NonDegenerate p),
      ⨆ (x₂ : Σ (q : ℕ), X₂.NonDegenerate q),
        Subcomplex.ofSimplexProd x₁.2.1 x₂.2.1 = ⊤ := by
  ext m ⟨x₁, x₂⟩
  simp only [Subpresheaf.iSup_obj, Set.iSup_eq_iUnion, Set.mem_iUnion, Sigma.exists,
    Subtype.exists, exists_prop, top_subpresheaf_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  have hx₁ : x₁ ∈ (⊤ : X₁.Subcomplex).obj _ := by simp
  have hx₂ : x₂ ∈ (⊤ : X₂.Subcomplex).obj _ := by simp
  rw [← Subcomplex.iSup_ofSimplex_nonDegenerate_eq_top] at hx₁ hx₂
  simp only [Subpresheaf.iSup_obj, Set.iSup_eq_iUnion, Set.iUnion_coe_set, Set.mem_iUnion,
    exists_prop] at hx₁ hx₂
  obtain ⟨⟨p, y₁, hy₁⟩, hx₁⟩ := hx₁
  obtain ⟨⟨q, y₂, hy₂⟩, hx₂⟩ := hx₂
  exact ⟨p, y₁, hy₁, q, y₂, hy₂, hx₁, hx₂⟩

lemma hasDimensionLT_prod (d₁ d₂ : ℕ) [X₁.HasDimensionLT d₁] [X₂.HasDimensionLT d₂]
    (n : ℕ) (hn : d₁ + d₂ ≤ n + 1) :
    HasDimensionLT (X₁ ⊗ X₂) n := by
  rw [hasDimensionLT_iff_subcomplex_top, ← subcomplex_prod_eq_top]
  simp only [hasDimensionLT_iSup_iff]
  rintro ⟨p, x₁⟩ ⟨q, x₂⟩
  apply hasDimensionLT_of_le _ (p + q + 1)
  have := X₁.dim_lt_of_nondegenerate x₁ d₁
  have := X₂.dim_lt_of_nondegenerate x₂ d₂
  omega

end SSet
