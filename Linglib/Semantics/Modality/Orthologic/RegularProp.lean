import Linglib.Semantics.Modality.Orthologic.Frames
import Linglib.Core.Order.Ortholattice
import Linglib.Core.Order.Orthoframe
import Mathlib.Data.SetLike.Basic

/-!
# Regular Propositions of a Compatibility Frame
[holliday-mandelkern-2024]

The `◇`-regular subsets of a compatibility frame `F` form an orthocomplemented
lattice. Rather than re-derive it, this file identifies that lattice with the
abstract concept lattice of the orthogonality relation `¬ compat`:
`CompatFrame.Regular F := Orthoframe.Regular F.toOrthoframe` (mathlib `Order.Concept`,
via `Core.Order.Orthoframe`), so the `OrthocomplementedLattice` structure and
Holliday–Mandelkern's Proposition 4.8 (`compl_compl`) come for free.

What this file contributes is the **decidable construction interface**: the
`IsRegular` predicate (a bounded-quantifier `Prop`, hence `decide`-able on finite
frames), its closure lemmas, the bridge `isRegular_iff_isExtent`, and the smart
constructor `CompatFrame.regOf` building a `Regular` element from a regularity proof.

## Main definitions
* `CompatFrame.toOrthoframe`, `CompatFrame.Regular`, `CompatFrame.regOf`.
* `isRegular_iff_isExtent` — `IsRegular F` is `IsExtent` of the orthogonality relation.
-/

namespace Orthologic

variable {S : Type*} {F : CompatFrame S}

/-! ### Closure-under-regularity helpers -/

/-- The orthocomplement of any set is regular (whether or not the original set is). -/
theorem orthoNeg_isRegular (F : CompatFrame S) (A : Set S) :
    IsRegular F (orthoNeg F A) := by
  intro x
  by_cases h : x ∈ orthoNeg F A
  · exact Or.inl h
  · right
    rw [mem_orthoNeg] at h
    push Not at h
    obtain ⟨y, hxy, hyA⟩ := h
    refine ⟨y, hxy, fun z hyz hzN => ?_⟩
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
      · exact ⟨y, hxy, fun z hyz hz => hy z hyz hz.1⟩
    · rcases hB x with hBx | ⟨y, hxy, hy⟩
      · exact absurd hBx hxB
      · exact ⟨y, hxy, fun z hyz hz => hy z hyz hz.2⟩

/-- The disjunction `disj F A B = orthoNeg F (orthoNeg F A ∩ orthoNeg F B)`
    is regular (immediate from `orthoNeg_isRegular`). -/
theorem disj_isRegular (F : CompatFrame S) (A B : Set S) :
    IsRegular F (disj F A B) :=
  orthoNeg_isRegular F _

/-- The empty set is regular (vacuously: take `y = x` by reflexivity). -/
theorem empty_isRegular (F : CompatFrame S) : IsRegular F (∅ : Set S) := by
  intro x
  exact Or.inr ⟨x, F.refl x, fun _ _ h => h.elim⟩

/-- The full set is regular (trivially). -/
theorem univ_isRegular (F : CompatFrame S) : IsRegular F (Set.univ : Set S) :=
  fun _ => Or.inl trivial

/-- The load-bearing involutivity: `orthoNeg² A = A` for regular `A`.
    [holliday-mandelkern-2024] Proposition 4.8. -/
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

/-- The orthogonality (incompatibility) orthoframe of a compatibility frame:
    `x ⊥ y ↔ ¬ compat x y`. Symmetry and irreflexivity come from symmetry and
    reflexivity of `compat`. -/
def CompatFrame.toOrthoframe (F : CompatFrame S) : Orthoframe S where
  ortho x y := ¬ F.compat x y
  ortho_symm := ⟨fun _ _ h hc => h hc.symm⟩
  ortho_irrefl := ⟨fun a h => h (F.refl a)⟩

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
  ⟨orthoNeg_orthoNeg_of_isRegular F, fun h => h ▸ orthoNeg_isRegular F _⟩

/-- The `◇`-regular sets of `F` are exactly the concept extents of its
    orthogonality relation; Holliday–Mandelkern's Proposition 4.8 is mathlib's
    `upperPolar_lowerPolar_upperPolar` (see `Core.Order.Orthoframe`). -/
theorem isRegular_iff_isExtent (F : CompatFrame S) (A : Set S) :
    IsRegular F A ↔ IsExtent F.toOrthoframe.ortho A := by
  rw [isRegular_iff_orthoNeg_orthoNeg, isExtent_iff,
      orthoNeg_eq_upperPolar, orthoNeg_eq_upperPolar,
      upperPolar_eq_lowerPolar F.toOrthoframe.ortho]

/-! ### The ortholattice of regular propositions -/

/-- The regular propositions of `F`: the ortholattice `Orthoframe.Regular` of its
    orthogonality orthoframe (the concept extents of `¬ compat`); Holliday–Mandelkern's
    Proposition 4.8 is mathlib's `upperPolar_lowerPolar_upperPolar`. The decidable
    `IsRegular` predicate is the construction interface — use `regOf` to build an
    element from a regularity proof (e.g. `by decide` on a finite frame). -/
abbrev CompatFrame.Regular (F : CompatFrame S) : Type _ := Orthoframe.Regular F.toOrthoframe

/-- Build a regular proposition from a set and an `IsRegular` proof. -/
def CompatFrame.regOf (F : CompatFrame S) (A : Set S) (h : IsRegular F A) : F.Regular :=
  Concept.ofIsExtent F.toOrthoframe.ortho A ((isRegular_iff_isExtent F A).mp h)

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

@[simp] theorem CompatFrame.Regular.coe_compl (A : F.Regular) :
    ((Aᶜ : F.Regular) : Set S) = orthoNeg F (A : Set S) := by
  show (Aᶜ).extent = orthoNeg F A.extent
  rw [orthoNeg_eq_upperPolar, Concept.extent_compl, ← Concept.upperPolar_extent]

end Orthologic
