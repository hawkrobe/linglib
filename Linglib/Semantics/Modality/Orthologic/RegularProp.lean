module

public import Linglib.Semantics.Modality.Orthologic.Frames
public import Linglib.Core.Order.Ortholattice
public import Linglib.Core.Order.Orthoframe
public import Mathlib.Data.SetLike.Basic

/-!
# Regular propositions of a compatibility frame

This file defines the ortholattice `CompatFrame.Regular F` of regular propositions of a
compatibility frame `F`. Rather than build the lattice by hand, it identifies the regular sets
with the extents of the concept lattice of the orthogonality relation `¬ compat`, so the
ortholattice structure, and Holliday and Mandelkern's involution `¬¬A = A` for regular `A`, come
from mathlib's `Order.Concept` through `Core/Order/Orthoframe.lean`.

## Main definitions

* `CompatFrame.toOrthoframe`: the orthogonality relation `¬ compat` of a frame.
* `CompatFrame.Regular`: the ortholattice of regular propositions.
* `CompatFrame.regOf`: the regular proposition of a set with a regularity proof.

## Main results

* `orthoNeg_isRegular`, `inter_isRegular`: regular sets are closed under `¬` and `∩`.
* `isRegular_iff_isExtent`: the regular sets are the concept extents of `¬ compat`.

## Implementation notes

The decidable predicate `IsRegular` is the construction interface: on a finite frame, `regOf`
builds a regular proposition from a proof by `decide`.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

namespace Orthologic

variable {S : Type*} {F : CompatFrame S}

/-! ### Closure properties of regular sets -/

/-- The orthocomplement of any set is regular, whether or not the set is. -/
theorem orthoNeg_isRegular (F : CompatFrame S) (A : Set S) :
    IsRegular F (orthoNeg F A) := by
  intro x
  by_cases h : x ∈ orthoNeg F A
  · exact Or.inl h
  · right
    rw [mem_orthoNeg] at h
    push Not at h
    obtain ⟨y, hxy, hyA⟩ := h
    refine ⟨y, hxy, fun z hyz hzN ↦ ?_⟩
    rw [mem_orthoNeg] at hzN
    exact hzN y (hyz.symm) hyA

/-- Regular sets are closed under intersection. -/
theorem inter_isRegular {F : CompatFrame S} {A B : Set S}
    (hA : IsRegular F A) (hB : IsRegular F B) : IsRegular F (A ∩ B) := by
  intro x
  by_cases h : x ∈ A ∩ B
  · exact Or.inl h
  · right
    rw [Set.mem_inter_iff, not_and_or] at h
    rcases h with hxA | hxB
    · rcases hA x with hAx | ⟨y, hxy, hy⟩
      · exact absurd hAx hxA
      · exact ⟨y, hxy, fun z hyz hz ↦ hy z hyz hz.1⟩
    · rcases hB x with hBx | ⟨y, hxy, hy⟩
      · exact absurd hBx hxB
      · exact ⟨y, hxy, fun z hyz hz ↦ hy z hyz hz.2⟩

/-- A disjunction is regular, being an orthocomplement. -/
theorem disj_isRegular (F : CompatFrame S) (A B : Set S) :
    IsRegular F (disj F A B) :=
  orthoNeg_isRegular F _

/-- The empty set is regular. -/
theorem empty_isRegular (F : CompatFrame S) : IsRegular F (∅ : Set S) := by
  intro x
  exact Or.inr ⟨x, F.refl x, fun _ _ h ↦ h.elim⟩

/-- The full set is regular. -/
theorem univ_isRegular (F : CompatFrame S) : IsRegular F (Set.univ : Set S) :=
  fun _ ↦ Or.inl trivial

/-- Orthocomplementation is involutive on regular sets, `¬¬A = A`
    ([holliday-mandelkern-2024] Proposition 4.8). -/
theorem orthoNeg_orthoNeg_of_isRegular (F : CompatFrame S) {A : Set S}
    (hA : IsRegular F A) : orthoNeg F (orthoNeg F A) = A := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    rcases hA x with hxA | ⟨y, hxy, hy⟩
    · exact hxA
    · exfalso
      rw [mem_orthoNeg] at hx
      have hyN : ¬ y ∈ orthoNeg F A := hx y hxy
      rw [mem_orthoNeg] at hyN
      push Not at hyN
      obtain ⟨z, hyz, hzA⟩ := hyN
      exact hy z hyz hzA
  · intro x hxA
    rw [mem_orthoNeg]
    intro y hxy
    rw [mem_orthoNeg]
    push Not
    exact ⟨x, hxy.symm, hxA⟩


/-! ### Bridge to the abstract orthoframe construction -/

open Order

/-- The orthoframe of a compatibility frame makes two possibilities orthogonal when they are
    incompatible. -/
def CompatFrame.toOrthoframe (F : CompatFrame S) : Orthoframe S where
  ortho x y := ¬ F.compat x y
  ortho_symm := ⟨fun _ _ h hc ↦ h hc.symm⟩
  ortho_irrefl := ⟨fun a h ↦ h (F.refl a)⟩

/-- `orthoNeg` is the `upperPolar` of the orthogonality relation. -/
theorem orthoNeg_eq_upperPolar (F : CompatFrame S) (A : Set S) :
    orthoNeg F A = upperPolar F.toOrthoframe.ortho A := by
  ext x
  constructor
  · intro hx a ha hc
    exact hx a hc.symm ha
  · intro hx y hxy hyA
    exact hx hyA hxy.symm

/-- `IsRegular` is the double-orthonegation fixed-point condition. -/
theorem isRegular_iff_orthoNeg_orthoNeg (F : CompatFrame S) (A : Set S) :
    IsRegular F A ↔ orthoNeg F (orthoNeg F A) = A :=
  ⟨orthoNeg_orthoNeg_of_isRegular F, fun h ↦ h ▸ orthoNeg_isRegular F _⟩

/-- The regular sets of `F` are exactly the concept extents of its orthogonality relation.
    [holliday-mandelkern-2024]'s Proposition 4.8 is then mathlib's
    `upperPolar_lowerPolar_upperPolar`. -/
theorem isRegular_iff_isExtent (F : CompatFrame S) (A : Set S) :
    IsRegular F A ↔ IsExtent F.toOrthoframe.ortho A := by
  rw [isRegular_iff_orthoNeg_orthoNeg, isExtent_iff,
      orthoNeg_eq_upperPolar, orthoNeg_eq_upperPolar,
      upperPolar_eq_lowerPolar F.toOrthoframe.ortho]

/-! ### The ortholattice of regular propositions -/

/-- The regular propositions of `F` form the ortholattice `Orthoframe.Regular` of its
    orthoframe, whose elements are the concept extents of `¬ compat`. -/
abbrev CompatFrame.Regular (F : CompatFrame S) : Type _ := Orthoframe.Regular F.toOrthoframe

/-- `F.regOf A h` is the regular proposition with underlying set `A`. -/
def CompatFrame.regOf (F : CompatFrame S) (A : Set S) (h : IsRegular F A) : F.Regular :=
  Concept.ofIsExtent F.toOrthoframe.ortho A ((isRegular_iff_isExtent F A).mp h)

/-- The underlying set of a regular proposition is regular. -/
theorem CompatFrame.Regular.isRegular (A : F.Regular) : IsRegular F A :=
  (isRegular_iff_isExtent F A).mpr A.isExtent_extent

@[simp] theorem CompatFrame.coe_regOf (A : Set S) (h : IsRegular F A) :
    (F.regOf A h : Set S) = A := rfl

@[simp] theorem CompatFrame.mem_regOf (A : Set S) (h : IsRegular F A) (x : S) :
    x ∈ F.regOf A h ↔ x ∈ A := Iff.rfl

@[simp] theorem CompatFrame.Regular.coe_inf (A B : F.Regular) :
    ((A ⊓ B : F.Regular) : Set S) = (A : Set S) ∩ (B : Set S) := rfl

@[simp] theorem CompatFrame.Regular.coe_top :
    ((⊤ : F.Regular) : Set S) = Set.univ := rfl

@[simp] theorem CompatFrame.Regular.coe_bot :
    ((⊥ : F.Regular) : Set S) = ∅ := Concept.extent_bot_eq_empty F.toOrthoframe.ortho

@[simp] theorem CompatFrame.Regular.coe_eq_empty {A : F.Regular} : (A : Set S) = ∅ ↔ A = ⊥ := by
  rw [← coe_bot, SetLike.coe_set_eq]

@[simp] theorem CompatFrame.Regular.coe_compl (A : F.Regular) :
    ((Aᶜ : F.Regular) : Set S) = orthoNeg F (A : Set S) := by
  show (Aᶜ).extent = orthoNeg F A.extent
  rw [orthoNeg_eq_upperPolar, Concept.extent_compl, ← Concept.upperPolar_extent]

end Orthologic
