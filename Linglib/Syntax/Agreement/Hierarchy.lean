import Mathlib.Order.Monotone.Defs
import Linglib.Syntax.Agreement.Target

/-!
# Semantic agreement along a hierarchy

This file defines the availability of semantic agreement at a position of the Agreement
Hierarchy, the hybrid nouns whose availability varies from position to position, and what it
is for a profile along a hierarchy to respect it.

A target agrees syntactically when its form follows the feature value the controller is
assigned, and semantically when it follows the controller's meaning. A hybrid noun, such as
Russian *vrač* 'doctor' denoting a woman or British English *committee*, admits both at some
positions, and the Agreement Hierarchy predicts that the likelihood of semantic agreement
never decreases from the attributive towards the personal pronoun. The positions of
`Agreement.Target` are ordered with the attributive on top, so a profile respects the
hierarchy when it is antitone on the positions where it is recorded.

## Main definitions

* `Agreement.Kind`: syntactic or semantic agreement.
* `Agreement.Availability`: the five degrees of availability of semantic agreement, from
  syntactic only to semantic only, linearly ordered.
* `Agreement.RespectsHierarchy`: a profile recorded at some positions of a hierarchy is
  antitone where it is recorded.
* `Agreement.Hybrid`: a hybrid noun, the availability of semantic agreement at the
  positions of a hierarchy for which there are data.

## Implementation notes

`RespectsHierarchy` takes any preorder of positions and any preorder of values, so that it
serves the Agreement Hierarchy on `Target`, the Predicate Hierarchy on the sub-positions of
the predicate, and refinements of the attributive position alike, and corpus proportions of
semantic agreement as well as availabilities. A position carrying no value is skipped: values
are compared only across comparable positions that both carry one.

## References

* [corbett-1979] — the Agreement Hierarchy
* [corbett-1983] — hierarchies, targets and controllers
* [corbett-1991] — the hierarchy applied to gender, chapter 8
* [corbett-2006] — the standard monograph on agreement
-/

namespace Agreement

/-- Whether an agreement form follows the feature value the controller is assigned or the
controller's meaning. -/
inductive Kind where
  | syntactic
  | semantic
  deriving DecidableEq, Repr, Fintype

/-- The availability of semantic agreement at a position of a hierarchy, the five categories
of [corbett-1991]'s summary of hybrid nouns, ordered by the likelihood of semantic
agreement. -/
inductive Availability where
  | syntacticOnly
  | mostlySyntactic
  | both
  | mostlySemantic
  | semanticOnly
  deriving DecidableEq, Repr, Fintype

namespace Availability

/-- The rank of an availability in the order of likelihood of semantic agreement. -/
def rank : Availability → ℕ
  | .syntacticOnly => 0
  | .mostlySyntactic => 1
  | .both => 2
  | .mostlySemantic => 3
  | .semanticOnly => 4

theorem rank_injective : Function.Injective rank := by decide

instance : LinearOrder Availability := LinearOrder.lift' rank rank_injective

/-- Which agreement an availability admits. -/
def Allows : Availability → Kind → Prop
  | .syntacticOnly, k => k = .syntactic
  | .semanticOnly, k => k = .semantic
  | _, _ => True

instance (a : Availability) (k : Kind) : Decidable (a.Allows k) := by
  cases a <;> simp only [Allows] <;> infer_instance

end Availability

section Hierarchy

variable {ι α : Type*} [Preorder ι] [Preorder α]

/-- A profile recording a value at some positions of a hierarchy respects it when the value
never decreases down the hierarchy: of two comparable positions that both carry a value, the
lower carries the larger. -/
def RespectsHierarchy (f : ι → Option α) : Prop :=
  ∀ ⦃i j⦄, i ≤ j → ∀ a ∈ f i, ∀ b ∈ f j, b ≤ a

instance [Fintype ι] [DecidableLE ι] [DecidableLE α] (f : ι → Option α) :
    Decidable (RespectsHierarchy f) := by
  unfold RespectsHierarchy; infer_instance

/-- A profile recorded at every position respects the hierarchy exactly when it is
antitone. -/
theorem respectsHierarchy_some_comp_iff_antitone {g : ι → α} :
    RespectsHierarchy (some ∘ g) ↔ Antitone g := by
  simp [RespectsHierarchy, Antitone]

end Hierarchy

/-- A hybrid noun, as the availability of semantic agreement at each position of a hierarchy
at which agreement in the feature applies and there are data; it respects the hierarchy when
`RespectsHierarchy` holds of it. -/
abbrev Hybrid (ι : Type*) := ι → Option Availability

end Agreement
