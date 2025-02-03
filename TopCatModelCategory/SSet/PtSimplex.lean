import TopCatModelCategory.SSet.Horn
import TopCatModelCategory.SSet.HomotopyBasic

universe u

open CategoryTheory Simplicial Limits

namespace SSet

variable (X : SSet.{u})

abbrev PtSimplex (n : ℕ) (x : X _[0]) : Type u :=
  Subcomplex.RelativeMorphism
    (subcomplexBoundary n) (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

namespace PtSimplex

variable {X} {n : ℕ} {x : X _[0]}

section

@[reassoc]
lemma comp_map_eq_const
    (s : X.PtSimplex n x)
    {Y : SSet.{u}} (φ : Y ⟶ Δ[n]) [Y.HasDimensionLT n] :
    φ ≫ s.map = const x := by
  refine (Subcomplex.lift φ ?_) ≫= s.comm
  apply le_antisymm (by simp)
  rw [← Subcomplex.image_le_iff, Subcomplex.image_top,
    standardSimplex.subcomplex_le_boundary_iff]
  intro h
  replace h : standardSimplex.id n ∈ (Subcomplex.range φ).obj _ := by simp [h]
  obtain ⟨x, hx⟩ := h
  have : ¬ (x ∈ Y.Degenerate n) := by
    intro hx'
    have := degenerate_map hx' φ
    simp [hx, mem_degenerate_iff_non_mem_nondegenerate,
      standardSimplex.non_degenerate_top_dim] at this
  simp [Y.degenerate_eq_top_of_hasDimensionLT n n (by rfl)] at this

@[reassoc (attr := simp)]
lemma δ_map (f : X.PtSimplex (n + 1) x) (i : Fin (n + 2)) :
    standardSimplex.map (SimplexCategory.δ i) ≫ f.map = const x :=
  comp_map_eq_const _ _

end

structure RelStruct (f g : X.PtSimplex n x) (i : Fin (n + 1)) where
  map : Δ[n + 1] ⟶ X
  δ_castSucc_map : standardSimplex.map (SimplexCategory.δ i.castSucc) ≫ map = f.map := by aesop_cat
  δ_succ_map : standardSimplex.map (SimplexCategory.δ i.succ) ≫ map = g.map := by aesop_cat
  δ_map_of_lt (j : Fin (n + 2)) (hj : j < i.castSucc) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x := by aesop_cat
  δ_map_of_gt (j : Fin (n + 2)) (hj : i.succ < j) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x := by aesop_cat

structure MulStruct (f g fg : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) where
  map : Δ[n + 2] ⟶ X
  δ_succ_succ_map : standardSimplex.map (SimplexCategory.δ (i.succ.succ)) ≫ map = f.map :=
    by aesop_cat
  δ_castSucc_castSucc_map : standardSimplex.map
    (SimplexCategory.δ (i.castSucc.castSucc)) ≫ map = g.map := by aesop_cat
  δ_castSucc_succ_map : standardSimplex.map (SimplexCategory.δ (i.castSucc.succ)) ≫ map =
    fg.map := by aesop_cat
  δ_map_of_lt (j : Fin (n + 3)) (hj : j < i.castSucc.castSucc) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x := by aesop_cat
  δ_map_of_gt (j : Fin (n + 3)) (hj : i.succ.succ < j) :
    standardSimplex.map (SimplexCategory.δ j) ≫ map = const x := by aesop_cat

namespace RelStruct

attribute [reassoc (attr := simp)] δ_castSucc_map δ_succ_map
  δ_map_of_lt δ_map_of_gt

def refl (f : X.PtSimplex n x) (i : Fin (n + 1)) : RelStruct f f i where
  map := standardSimplex.map (SimplexCategory.σ i) ≫ f.map
  δ_castSucc_map := by
    simp [← Functor.map_comp_assoc, SimplexCategory.δ_comp_σ_self]
  δ_succ_map := by
    simp [← Functor.map_comp_assoc, SimplexCategory.δ_comp_σ_succ]
  δ_map_of_lt j hj := by
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · simp at hj
    . obtain ⟨j, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
      · obtain _ | n := n
        · fin_cases i
        · rw [← Functor.map_comp_assoc,
            SimplexCategory.δ_comp_σ_of_le
            (by simpa only[← Fin.succ_castSucc,
              Fin.castSucc_lt_succ_iff] using hj),
            Functor.map_comp_assoc, δ_map, comp_const]
      · have := Fin.ne_last_of_lt hj
        simp at this
  δ_map_of_gt j hj := by
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · obtain _ | n := n
      · fin_cases i
      · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
        · simp at hj
        · rw [← Functor.map_comp_assoc,
            SimplexCategory.δ_comp_σ_of_gt (by simpa using hj),
            Functor.map_comp_assoc, δ_map, comp_const]
    · simp only [Fin.succ_last, Nat.succ_eq_add_one] at hj
      have := Fin.ne_last_of_lt hj
      simp at this

end RelStruct

namespace MulStruct

attribute [reassoc (attr := simp)] δ_succ_succ_map δ_castSucc_castSucc_map
  δ_castSucc_succ_map δ_map_of_lt δ_map_of_gt

end MulStruct

def relStructCastSuccEquivMulStruct {f g : X.PtSimplex (n + 1) x} {i : Fin (n + 1)} :
    RelStruct f g i.castSucc ≃ MulStruct .const f g i where
  toFun h :=
    { map := h.map
      δ_succ_succ_map := h.δ_map_of_gt i.succ.succ (by simp)
      δ_map_of_gt j hj := h.δ_map_of_gt j (lt_trans (by simp) hj) }
  invFun h :=
    { map := h.map
      δ_map_of_gt j hj := by
        rw [Fin.succ_castSucc, Fin.castSucc_lt_iff_succ_le] at hj
        obtain rfl | hj := hj.eq_or_lt
        · exact h.δ_succ_succ_map
        · exact h.δ_map_of_gt j hj }
  left_inv _ := rfl
  right_inv _ := rfl

def relStructSuccEquivMulStruct {f g : X.PtSimplex (n + 1) x} {i : Fin (n + 1)} :
    RelStruct f g i.succ ≃ MulStruct g .const f i where
  toFun h :=
    { map := h.map
      δ_castSucc_succ_map := h.δ_castSucc_map
      δ_map_of_lt j hj := h.δ_map_of_lt j (lt_trans hj (by simp)) }
  invFun h :=
    { map := h.map
      δ_castSucc_map := h.δ_castSucc_succ_map
      δ_map_of_lt j hj := by
        rw [← Fin.succ_castSucc] at hj
        obtain rfl | hj := (Fin.le_castSucc_iff.2 hj).eq_or_lt
        · exact h.δ_castSucc_castSucc_map
        · exact h.δ_map_of_lt j hj }
  left_inv _ := rfl
  right_inv _ := rfl

namespace MulStruct

def oneMul (f : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    MulStruct .const f f i :=
  relStructCastSuccEquivMulStruct (RelStruct.refl f i.castSucc)

def mulOne (f : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    MulStruct f .const f i :=
  relStructSuccEquivMulStruct (RelStruct.refl f i.succ)

end MulStruct

namespace MulStruct

noncomputable def assoc {f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f₀₃ : X.PtSimplex (n + 1) x} (i : Fin (n + 1))
    (h₀₂ : MulStruct f₀₁ f₁₂ f₀₂ i)
    (h₁₃ : MulStruct f₁₂ f₂₃ f₁₃ i)
    (h : MulStruct f₀₁ f₁₃ f₀₃ i) :
    MulStruct f₀₂ f₂₃ f₀₃ i := by
  apply Nonempty.some
  sorry
  --obtain ⟨α, hα₁, hα₂, hα₃⟩ :=
  --  subcomplexHorn₃₁.exists_desc h₁₃.map h.map h₀₂.map (by simp) (by simp) (by simp)
  --obtain ⟨β, hβ⟩ := anodyneExtensions.exists_lift_of_isFibrant α
  --  (anodyneExtensions.subcomplexHorn_ι_mem 2 1)

end MulStruct

end PtSimplex

end SSet
