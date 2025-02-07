import TopCatModelCategory.SSet.NonDegenerateProdSimplex

open CategoryTheory Simplicial MonoidalCategory Opposite

namespace SSet

namespace prodStandardSimplex₁

variable {n : ℕ}

noncomputable def nonDegenerateEquiv :
    Fin (n + 1) ≃ (Δ[n] ⊗ Δ[1] : SSet.{u}).NonDegenerate (n + 1) :=
  prodStandardSimplex.nonDegenerateEquiv₁.{u}.trans
    (nonDegenerateEquivOfIso (β_ _ _) _)

@[simp]
lemma nonDegenerateEquiv_fst (i : Fin (n + 1)) :
    (nonDegenerateEquiv i).1.1 =
      (standardSimplex.objEquiv _ _).symm (SimplexCategory.σ i) := rfl

@[simp]
lemma nonDegenerateEquiv_snd (i : Fin (n + 1)) :
    (nonDegenerateEquiv i).1.2 =
      standardSimplex.objMk₁ i.succ.castSucc := rfl

noncomputable def filtration (j : Fin (n + 1)) : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  ⨆ (i : ({i // i ≤ j} : Type)), .ofSimplex (nonDegenerateEquiv i.1).1

lemma ofSimplex_le_filtration {i j : Fin (n + 1)} (hij : i ≤ j) :
    .ofSimplex (nonDegenerateEquiv i).1 ≤ filtration.{u} j :=
  le_iSup (fun (i : {i // i ≤ j}) ↦
    Subcomplex.ofSimplex (nonDegenerateEquiv i.1).1) ⟨i, hij⟩

variable (n) in
lemma filtration_zero :
    filtration.{u} (0 : Fin (n + 1)) = .ofSimplex (nonDegenerateEquiv 0).1 :=
  le_antisymm (by simp [filtration]) (ofSimplex_le_filtration.{u} (by rfl))

noncomputable def intersectionNondeg (i j : Fin (n + 1)) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  .ofSimplex (nonDegenerateEquiv i).1 ⊓ .ofSimplex (nonDegenerateEquiv j).1

-- TODO: show this is representable by Δ[n]
noncomputable abbrev interSucc (j : Fin n) : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
    intersectionNondeg j.castSucc j.succ

lemma le_interSucc (i : Fin (n + 1)) (j : Fin n) (hij : i ≤ j.castSucc) :
    intersectionNondeg.{u} i j.succ ≤ interSucc j := by
  sorry

section

lemma sq (j : Fin n) :
    Subcomplex.Sq (interSucc j) (filtration.{u} j.castSucc)
      (.ofSimplex (nonDegenerateEquiv j.succ).1)
      (filtration.{u} j.succ) where
  min_eq := by
    apply le_antisymm
    · dsimp [filtration]
      rw [Subcomplex.iSup_inf, iSup_le_iff, Subtype.forall]
      intro i hi
      exact le_interSucc _ _ hi
    · dsimp [interSucc, intersectionNondeg]
      simp only [le_inf_iff, inf_le_right, and_true]
      exact inf_le_left.trans (ofSimplex_le_filtration (by rfl))
  max_eq := by
    apply le_antisymm
    · rw [filtration, sup_le_iff, iSup_le_iff, Subtype.forall]
      constructor
      · intro i hi
        exact ofSimplex_le_filtration (hi.trans (j.castSucc_le_succ))
      · exact ofSimplex_le_filtration (by rfl)
    · rw [filtration, iSup_le_iff, Subtype.forall]
      intro i hi
      obtain hi | rfl := hi.lt_or_eq
      · refine le_trans ?_ le_sup_left
        exact ofSimplex_le_filtration (Fin.le_castSucc_iff.2 hi)
      · exact le_sup_right

end

end prodStandardSimplex₁

end SSet
