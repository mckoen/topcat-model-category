import TopCatModelCategory.SSet._007F_filtration
import TopCatModelCategory.SSet._Order

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

open Subcomplex stdSimplex

variable {n : ℕ} (a b : Fin (n + 2))

namespace τ

/-- for `0 ≤ a ≤ b ≤ n`, the image of `Λ[n + 2, a + 1]` under `gab : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
def innerHornImage (a b : Fin (n + 2)) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (horn (n + 2) a.succ).image (g a b)

/-- for `0 ≤ a ≤ b ≤ n`, the image of `∂Δ[n + 2]` under `gab : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
def boundaryImage : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (boundary (n + 2)).image (g a b)

/-- image of the i-th face under some f : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] -/
@[simp]
noncomputable
def faceImage (i : Fin (n + 3)) (f : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (face {i}ᶜ).image f

-- image of Λ[n + 2, a + 1] under (g a b) is the union of the image under g of all faces except
-- the (a + 1)-th
lemma innerHornImage_eq_iSup : innerHornImage a b =
    ⨆ (j : ({a.succ}ᶜ : Set (Fin (n + 3)))), faceImage j.1 (g a b) := by
  simp only [innerHornImage, horn_eq_iSup, image_iSup, faceImage]

lemma boundaryImage_eq_iSup : boundaryImage a b =
    ⨆ (j : Fin (n + 3)), faceImage j.1 (g a b) := by
  simp only [boundaryImage, boundary_eq_iSup, image_iSup, faceImage,
    Fin.cast_val_eq_self]

lemma innerHornImage_le_σ : innerHornImage a b ≤ τ a b := by
  rw [innerHornImage_eq_iSup]
  exact iSup_le fun _ ↦ image_le_range _ _

lemma faceImage_le_σ (j : Fin (n + 3)) :
    faceImage j (g a b) ≤ τ a b := image_le_range _ _

section a_lt_b

variable (a b : Fin (n + 1)) (hab : a < b)

/-- each face of `τab` except the `a`-th, `(a+1)`-th, `(b+1)`-th, and `(b+2)`-th is contained
  in `(boundary n).unionProd (horn 2 1)`. -/
lemma faceImage_le_unionProd (j : Fin (n + 3))
    (ha : ¬j = a.castSucc.castSucc) (ha' : ¬j = a.succ.castSucc)
    (hb : ¬j = b.succ.castSucc) (hb' : ¬j = b.succ.succ) :
    faceImage j (g a.castSucc b.castSucc) ≤ (boundary n).unionProd (horn 2 1) := sorry

end a_lt_b

end τ
