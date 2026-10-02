/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.UpperLower.Finset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.DeriveFintype

/-!
# Containment feature pairs

A containment pair is the set of positive values of two bivalent features, an outer feature and
an inner one depending on it. It passes the containment filter when the inner feature entails the
outer, that is, when its positive features form a lower set of the two-element chain. The lower
sets of a chain are its initial segments and number one more than the chain
(`Fintype.card_subtype_isLowerSet`), so two dependent features give exactly three cells, linearly
ordered by specification. Person, number and gender features instantiate the same theory over
their own chains; this file is the anonymous instance, the cell type of the φ-feature
competitions.

## Main definitions

* `Agreement.ContainmentPair`: the positive features of a valuation.
* `ContainmentPair.maximal`, `ContainmentPair.intermediate`, `ContainmentPair.minimal`: the three
  cells, the initial segments of the chain.
* `ContainmentPair.specLevel`: the number of positive features.

## Main results

* `ContainmentPair.classification`: every pair passing the filter is one of the three cells.
* `ContainmentPair.card_wellFormed`: there are three such cells.

## Implementation notes

Harley and Ritter read a dependency in a feature geometry as morphological implication, which the
lower-set condition states for a chain. The filter is descriptive and not Harbour's calculus,
which rejects it and uses the filtered cell as the quadripartition exclusive
(`Studies/Harbour2016.lean`).

## References

* [harley-ritter-2002]
* [harbour-2016]
-/

@[expose] public section

namespace Agreement

namespace ContainmentPair

/-- The two features, the inner depending on the outer. -/
inductive Feature where
  | outer
  | inner
  deriving DecidableEq, Repr, Fintype

/-- `Feature.rank` places the outer feature below the inner one on the dependency chain. -/
def Feature.rank : Feature → Fin 2
  | .outer => 0
  | .inner => 1

instance : LinearOrder Feature := LinearOrder.lift' Feature.rank (by decide)

instance : LocallyFiniteOrderBot Feature := Fintype.toLocallyFiniteOrderBot

end ContainmentPair

/-- A valuation of two dependent bivalent features is the set of its positive ones. -/
abbrev ContainmentPair := Finset ContainmentPair.Feature

namespace ContainmentPair

open Finset

/-! ### The three cells -/

/-- The least specified cell has no positive feature, as third person and plural. -/
def minimal : ContainmentPair := ∅

/-- The intermediate cell has the outer feature alone, as second person and dual. -/
def intermediate : ContainmentPair := Iic .outer

/-- The most specified cell has both features, as first person and singular. -/
def maximal : ContainmentPair := Iic .inner

theorem intermediate_eq : intermediate = {.outer} := by decide

theorem maximal_eq : maximal = univ := by decide

theorem isLowerSet_minimal : IsLowerSet (↑minimal : Set Feature) := isLowerSet_coe_empty

theorem isLowerSet_intermediate : IsLowerSet (↑intermediate : Set Feature) :=
  isLowerSet_coe_Iic _

theorem isLowerSet_maximal : IsLowerSet (↑maximal : Set Feature) := isLowerSet_coe_Iic _

/-- The inner feature without the outer fails the containment filter. -/
theorem not_isLowerSet_singleton_inner :
    ¬ IsLowerSet (↑({.inner} : ContainmentPair) : Set Feature) := by
  decide

/-- Every pair passing the containment filter is one of the three cells. -/
theorem classification (p : ContainmentPair) (h : IsLowerSet (↑p : Set Feature)) :
    p = maximal ∨ p = intermediate ∨ p = minimal := by
  rcases h.eq_empty_or_eq_Iic with rfl | ⟨a, rfl⟩
  · exact .inr (.inr rfl)
  · cases a
    · exact .inr (.inl rfl)
    · exact .inl rfl

/-- Two dependent features yield exactly three cells. -/
theorem card_wellFormed :
    Fintype.card {p : ContainmentPair // IsLowerSet (↑p : Set Feature)} = 3 := by
  rw [Fintype.card_subtype_isLowerSet]; rfl

/-! ### The specification chain -/

/-- The specification level of a pair is its number of positive features. -/
def specLevel (p : ContainmentPair) : ℕ := p.card

@[simp] theorem spec_maximal : maximal.specLevel = 2 := by decide
@[simp] theorem spec_intermediate : intermediate.specLevel = 1 := by decide
@[simp] theorem spec_minimal : minimal.specLevel = 0 := by decide

/-- A pair has at most its two features. -/
theorem specLevel_le_two (p : ContainmentPair) : p.specLevel ≤ 2 :=
  (Finset.card_le_univ p).trans (by decide)

end ContainmentPair

end Agreement
