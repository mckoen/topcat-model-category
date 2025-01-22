import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.Data.Set.Lattice
import TopCatModelCategory.Multiequalizer

universe v u

open CategoryTheory Limits

namespace Lattice

variable {T : Type u} (x₁ x₂ x₃ x₄ : T) [Lattice T]

structure BicartSq : Prop where
  max_eq : x₂ ⊔ x₃ = x₄
  min_eq : x₂ ⊓ x₃ = x₁

namespace BicartSq

variable {x₁ x₂ x₃ x₄ : T} (sq : BicartSq x₁ x₂ x₃ x₄)

include sq
lemma le₁₂ : x₁ ≤ x₂ := by rw [← sq.min_eq]; exact inf_le_left
lemma le₁₃ : x₁ ≤ x₃ := by rw [← sq.min_eq]; exact inf_le_right
lemma le₂₄ : x₂ ≤ x₄ := by rw [← sq.max_eq]; exact le_sup_left
lemma le₃₄ : x₃ ≤ x₄ := by rw [← sq.max_eq]; exact le_sup_right

-- the associated commutative square in `T`
lemma commSq : CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) := ⟨rfl⟩

end BicartSq

end Lattice

@[simps obj map]
def Set.toTypes {X : Type u} : Set X ⥤ Type u where
  obj S := S
  map {S T} f := fun ⟨x, hx⟩ ↦ ⟨x, leOfHom f hx⟩

namespace CategoryTheory.Limits.Types

section Pushouts

section

variable {X X' : Type u} (f : X' → X) (A B : Set X) (A' B' : Set X')
  (hA' : A' = f ⁻¹' A ⊓ B') (hB : B = A ⊔ f '' B')

def pushoutCoconeOfPullbackSets :
    PushoutCocone
      (fun ⟨a', ha'⟩ ↦ ⟨f a', by
        rw [hA'] at ha'
        exact ha'.1⟩ : _ ⟶ (A : Type u) )
      (Set.toTypes.map (homOfLE (by rw [hA']; exact inf_le_right)) : (A' : Type u) ⟶ B') :=
  PushoutCocone.mk (W := (B : Type u))
    (Set.toTypes.map (homOfLE (by rw [hB]; exact le_sup_left)) : (A : Type u) ⟶ B)
    (fun ⟨b', hb'⟩ ↦ ⟨f b', by rw [hB]; exact Or.inr (by aesop)⟩) rfl

variable (T : Set X)

open Classical in
noncomputable def isColimitPushoutCoconeOfPullbackSets
    (hf : Function.Injective (fun (b : (A'ᶜ : Set _)) ↦ f b)) :
    IsColimit (pushoutCoconeOfPullbackSets f A B A' B' hA' hB) := by
  let g₁ : (A' : Type u) ⟶ A := fun ⟨a', ha'⟩ ↦ ⟨f a', by
        rw [hA'] at ha'
        exact ha'.1⟩
  let g₂ : (A' : Type u) ⟶ B' :=
    (Set.toTypes.map (homOfLE (by rw [hA']; exact inf_le_right)) : (A' : Type u) ⟶ B')
  have imp {b : X} (hb : b ∈ B) (hb' : b ∉ A) : b ∈ f '' B' := by
    simp only [hB, Set.sup_eq_union, Set.mem_union] at hb
    tauto
  let desc (s : PushoutCocone g₁ g₂) : (B : Type u) ⟶ s.pt := fun ⟨b, hb⟩ ↦
    if hb' : b ∈ A then
      s.inl ⟨b, hb'⟩
    else
      s.inr ⟨(imp hb hb').choose, (imp hb hb').choose_spec.1⟩
  have inl_desc_apply (s) (a : A) : desc s ⟨a, by
    rw [hB]
    exact Or.inl a.2⟩ = s.inl a := dif_pos a.2
  have inr_desc_apply (s) (b' : B') : desc s ⟨f b', by
      rw [hB]
      exact Or.inr ⟨b'.1, b'.2, rfl⟩⟩ = s.inr b' := by
    obtain ⟨b', hb'⟩ := b'
    dsimp [desc]
    split_ifs with hb''
    · exact congr_fun s.condition ⟨b', by rw [hA']; exact ⟨hb'', hb'⟩⟩
    · apply congr_arg
      ext
      have hb''' : f b' ∈ B := by
        rw [hB]
        exact Or.inr ⟨b', hb', rfl⟩
      dsimp
      subst hA'
      refine congr_arg Subtype.val (@hf ⟨(imp hb''' hb'').choose, ?_⟩ ⟨b', ?_⟩
        (imp hb''' hb'').choose_spec.2)
      · simp only [Set.inf_eq_inter, Set.mem_compl_iff, Set.mem_inter_iff, not_and]
        refine fun h _ ↦ hb'' ?_
        rw [← (imp hb''' hb'').choose_spec.2]
        exact h
      · simp only [Set.inf_eq_inter, Set.mem_compl_iff, Set.mem_inter_iff, not_and]
        exact fun h ↦ (hb'' h).elim
  refine PushoutCocone.IsColimit.mk _ desc
    (fun s ↦ by ext; apply inl_desc_apply)
    (fun s ↦ by ext; apply inr_desc_apply)
    (fun s m h₁ h₂ ↦ ?_)
  ext ⟨b, hb⟩
  dsimp
  by_cases hb' : b ∈ f '' B'
  · obtain ⟨b', hb', rfl⟩ := hb'
    exact (congr_fun h₂ ⟨b', hb'⟩).trans (inr_desc_apply s ⟨b', hb'⟩ ).symm
  · have hb : b ∈ A := by
      simp only [hB, Set.sup_eq_union, Set.mem_union] at hb
      tauto
    exact (congr_fun h₁ ⟨b, hb⟩).trans (inl_desc_apply s ⟨b, hb⟩).symm

end

section

variable {X : Type u} {A₁ A₂ A₃ A₄ : Set X} (sq : Lattice.BicartSq A₁ A₂ A₃ A₄)

def pushoutCoconeOfBicartSqOfSets :
    PushoutCocone (Set.toTypes.map (homOfLE sq.le₁₂))
      (Set.toTypes.map (homOfLE sq.le₁₃)) :=
  PushoutCocone.mk _ _ (sq.commSq.map Set.toTypes).w

noncomputable def isColimitPushoutCoconeOfBicartSqOfSets :
    IsColimit (pushoutCoconeOfBicartSqOfSets sq) :=
  isColimitPushoutCoconeOfPullbackSets id A₂ A₄ A₁ A₃
    sq.min_eq.symm (by simpa using sq.max_eq.symm)
      (by rintro ⟨a, _⟩ ⟨b, _⟩ rfl; rfl)

end

end Pushouts

end CategoryTheory.Limits.Types

namespace CompleteLattice

variable {T : Type*} [CompleteLattice T] {ι : Type*} (X : T) (U : ι → T) (V : ι → ι → T)

structure MulticoequalizerDiagram : Prop where
  hX : X = ⨆ (i : ι), U i
  hV (i j : ι) : V i j = U i ⊓ U j

namespace MulticoequalizerDiagram

variable {X U V} (d : MulticoequalizerDiagram X U V)

@[simps]
def multispanIndex : MultispanIndex T where
  L := ι × ι
  R := ι
  fstFrom := Prod.fst
  sndFrom := Prod.snd
  left := fun ⟨i, j⟩ ↦ V i j
  right := U
  fst _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_left)
  snd _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_right)

@[simps! pt]
def multicofork : Multicofork d.multispanIndex :=
  Multicofork.ofπ _ X (fun i ↦ homOfLE (by simpa only [d.hX] using le_iSup U i))
    (fun _ ↦ rfl)

variable [Preorder ι]

@[simps]
def multispanIndex' : MultispanIndex T where
  L := { (i, j) : ι × ι | i < j }
  R := ι
  fstFrom := fun ⟨⟨i, j⟩, _⟩ ↦ i
  sndFrom := fun ⟨⟨i, j⟩, _⟩ ↦ j
  left := fun ⟨⟨i, j⟩, _⟩ ↦ V i j
  right := U
  fst _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_left)
  snd _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_right)

@[simps! pt]
def multicofork' : Multicofork d.multispanIndex' :=
  Multicofork.ofπ _ X (fun i ↦ homOfLE (by simpa only [d.hX] using le_iSup U i))
    (fun _ ↦ rfl)


end MulticoequalizerDiagram

end CompleteLattice

namespace CategoryTheory.Limits

namespace Types

variable {T : Type u} {ι : Type v} {X : Set T} {U : ι → Set T} {V : ι → ι → Set T}
  (d : CompleteLattice.MulticoequalizerDiagram X U V)

namespace isColimitMulticoforkMapSetToTypes

include d in
lemma exists_index (x : X) : ∃ (i : ι), x.1 ∈ U i := by
  obtain ⟨x, hx⟩ := x
  rw [d.hX] at hx
  aesop

noncomputable def index (x : X) : ι := (exists_index d x).choose

lemma mem (x : X) : x.1 ∈ U (index d x) := (exists_index d x).choose_spec

section

variable {d} (s : Multicofork (d.multispanIndex.map Set.toTypes))

noncomputable def desc (x : X) : s.pt := s.π (index d x) ⟨x, mem d x⟩

lemma fac_apply (i : ι) (u : U i) :
    desc s ⟨u, by simp only [d.hX]; aesop⟩ = s.π i u :=
  congr_fun (s.condition ⟨index d _, i⟩) ⟨u, by
    dsimp
    simp only [d.hV, Set.inf_eq_inter, Set.mem_inter_iff, Subtype.coe_prop, and_true]
    apply mem⟩

end

section

variable [LinearOrder ι] {d} (s : Multicofork (d.multispanIndex'.map Set.toTypes))

noncomputable def desc' (x : X) : s.pt := s.π (index d x) ⟨x, mem d x⟩

lemma condition'_apply (x : T) (i j : ι) (hi : x ∈ U i) (hj : x ∈ U j) :
    s.π i ⟨x, hi⟩ = s.π j ⟨x, hj⟩ := by
  obtain hij | rfl | hij := lt_trichotomy i j
  · refine congr_fun (s.condition ⟨⟨i, j⟩, hij⟩) ⟨x, ?_⟩
    dsimp
    rw [d.hV]
    exact ⟨hi, hj⟩
  · rfl
  · refine congr_fun (s.condition ⟨⟨j, i⟩, hij⟩).symm ⟨x, ?_⟩
    dsimp
    rw [d.hV]
    exact ⟨hj, hi⟩

lemma fac'_apply (i : ι) (u : U i) :
    desc' s ⟨u, by simp only [d.hX]; aesop⟩ = s.π i u := by
  apply condition'_apply

end

end isColimitMulticoforkMapSetToTypes

open isColimitMulticoforkMapSetToTypes in
noncomputable def isColimitMulticoforkMapSetToTypes :
    IsColimit (d.multicofork.map Set.toTypes) :=
  Multicofork.IsColimit.mk _ desc (fun s i ↦ by ext x; apply fac_apply) (fun s m hm ↦ by
    ext x
    exact congr_fun (hm (index d x)) ⟨x.1, mem d x⟩)

open isColimitMulticoforkMapSetToTypes in
noncomputable def isColimitMulticoforkMapSetToTypes' [LinearOrder ι] :
    IsColimit (d.multicofork'.map Set.toTypes) :=
  Multicofork.IsColimit.mk _ desc' (fun s i ↦ by ext x; apply fac'_apply) (fun s m hm ↦ by
    ext x
    exact congr_fun (hm (index d x)) ⟨x.1, mem d x⟩)

end Types

end CategoryTheory.Limits
