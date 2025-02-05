import TopCatModelCategory.SSet.PtSimplex

open HomotopicalAlgebra CategoryTheory Simplicial Limits Opposite

universe u

namespace SSet

namespace KanComplex

def π (n : ℕ) (X : SSet.{u}) (x : X _[0]) : Type u :=
  Subcomplex.RelativeMorphism.HomotopyClass
    (subcomplexBoundary n) (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

def π.mk {n : ℕ} {X : SSet.{u}} {x : X _[0]}
  (f : X.PtSimplex n x) : π n X x := f.homotopyClass

lemma π.mk_surjective {n : ℕ} {X : SSet.{u}} {x : X _[0]} :
    Function.Surjective (π.mk : _ → π n X x) :=
  Quot.mk_surjective

instance (n : ℕ) (X : SSet.{u}) (x : X _[0]) : One (π n X x) where
  one := Subcomplex.RelativeMorphism.const.homotopyClass

section

variable {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
  (x : X _[0]) (y : Y _[0]) (h : f.app _ x = y)

def mapπ (p : π n X x) : π n Y y :=
  p.postcomp (.ofSimplex₀ f x y h) (by rw [comp_const])

variable {Z : SSet.{u}} (g : Y ⟶ Z) (z : Z _[0]) (h' : g.app _ y = z)

lemma mapπ_mapπ (p : π n X x) :
    mapπ g n y z h' (mapπ f n x y h p) =
      mapπ (f ≫ g) n x z (by simp [h, h']) p := by
  obtain ⟨h, rfl⟩ := p.eq_homotopyClass
  rfl

lemma mapπ_comp_mapπ :
    mapπ g n y z h' ∘ mapπ f n x y h = mapπ (f ≫ g) n x z (by simp [h, h']) := by
  ext
  apply mapπ_mapπ

@[simp]
lemma mapπ_id (p : π n X x) :
    mapπ (𝟙 X) n x x rfl p = p := by
  obtain ⟨h, rfl⟩ := p.eq_homotopyClass
  rfl

def mapπEquivOfIso (e : X ≅ Y) (n : ℕ) (x : X _[0]) (y : Y _[0]) (h : e.hom.app _ x = y) :
    π n X x ≃ π n Y y where
  toFun := mapπ e.hom n x y h
  invFun := mapπ e.inv n y x (by simp [← h])
  left_inv _ := by simp [mapπ_mapπ]
  right_inv _ := by simp [mapπ_mapπ]

end

namespace π

variable {X : SSet.{u}}  {x : X _[0]} {n : ℕ} [IsFibrant X]

lemma mk_eq_mk_iff (p q : X.PtSimplex n x) :
    mk p = mk q ↔ Nonempty (p.RelStruct₀ q) := sorry

lemma mk_eq_one_iff (p : X.PtSimplex n x) :
    mk p = 1 ↔ Nonempty (p.RelStruct₀ .const) :=
  mk_eq_mk_iff _ _

noncomputable def mul' (p q : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    X.PtSimplex (n + 1) x :=
  (PtSimplex.MulStruct.nonempty p q i).choose

noncomputable def mulStruct (p q : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    PtSimplex.MulStruct p q (mul' p q i) i :=
  (PtSimplex.MulStruct.nonempty p q i).choose_spec.some

noncomputable def mul (i : Fin (n + 1)) (g₁ g₂ : π (n + 1) X x) : π (n + 1) X x := by
  refine Quot.lift₂ (fun p q ↦ mk (mul' p q i)) ?_ ?_ g₁ g₂
  · rintro p q q' ⟨h : q.Homotopy q'⟩
    dsimp
    sorry
  · rintro p p' q ⟨h : p.Homotopy p'⟩
    dsimp
    sorry

lemma mul_mk_eq_iff {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x} {i : Fin (n + 1)} :
    mul i (mk g₁) (mk g₂) = mk g₁₂ ↔
      Nonempty (PtSimplex.MulStruct g₁ g₂ g₁₂ i) := by
  sorry

lemma mul_eq_of_mulStruct {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : PtSimplex.MulStruct g₁ g₂ g₁₂ i) : mul i (mk g₁) (mk g₂) = mk g₁₂ := by
  rw [mul_mk_eq_iff]
  exact ⟨h⟩

lemma mul_assoc (i : Fin (n + 1)) (g₁ g₂ g₃ : π (n + 1) X x) :
    mul i (mul i g₁ g₂) g₃ = mul i g₁ (mul i g₂ g₃) := by
  obtain ⟨p₁, rfl⟩ := g₁.mk_surjective
  obtain ⟨p₂, rfl⟩ := g₂.mk_surjective
  obtain ⟨p₃, rfl⟩ := g₃.mk_surjective
  exact mul_eq_of_mulStruct
    (PtSimplex.MulStruct.assoc (mulStruct p₁ p₂ i) (mulStruct p₂ p₃ i)
      (mulStruct p₁ (mul' p₂ p₃ i) i))

@[simp]
lemma one_mul (i : Fin (n + 1)) (g : π (n + 1) X x) :
    mul i 1 g = g := by
  obtain ⟨p, rfl⟩ := g.mk_surjective
  exact mul_eq_of_mulStruct (PtSimplex.MulStruct.oneMul p i)

@[simp]
lemma mul_one (i : Fin (n + 1)) (g : π (n + 1) X x) :
    mul i g 1 = g := by
  obtain ⟨p, rfl⟩ := g.mk_surjective
  exact mul_eq_of_mulStruct (PtSimplex.MulStruct.mulOne p i)

noncomputable instance : Mul (π (n + 1) X x) where
  mul := mul 0

noncomputable instance : Monoid (π (n + 1) X x) where
  mul_assoc := mul_assoc 0
  one_mul := one_mul 0
  mul_one := mul_one 0

end π

end KanComplex

end SSet
