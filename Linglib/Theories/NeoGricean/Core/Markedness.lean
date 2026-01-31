/-
# Neo-Gricean Markedness Infrastructure

Formalization of markedness computation for Rett (2015) Chapters 5-6.

## Key Insight

Markedness is COMPUTED from objective properties, not stipulated in the lexicon.
This module provides the NeoGricean-internal machinery for determining which
member of an antonym pair is marked.

## Markedness Criteria

Following Horn (1984) and Rett (2015):

1. **Morphological complexity**: un-happy > happy (more morphemes = marked)
2. **Scale direction**: negative pole is typically marked
3. **Distributional asymmetry**: marked forms are more restricted

The key point: these are objective, measurable properties. Different theories
(NeoGricean vs. RSA) can use different mechanisms to derive the same effects.

## References

- Horn, L. (1984). Toward a new taxonomy for pragmatic inference.
- Rett, J. (2015). The Semantics of Evaluativity, Chapters 5-6.
- Bierwisch, M. (1989). The semantics of gradation.
- Cruse, D. A. (1986). Lexical Semantics.
-/

import Linglib.Theories.Montague.Lexicon.Adjectives.Theory
import Linglib.Fragments.English.Predicates.Adjectival
import Mathlib.Data.Rat.Defs

namespace NeoGricean.Markedness

open Montague.Lexicon.Adjectives
open Montague.Lexicon.Degrees
open Fragments.English.Predicates.Adjectival (tall short happy unhappy)

-- ============================================================================
-- PART 1: Morphological Structure
-- ============================================================================

/--
Morphological structure of an adjective form.

Tracks properties relevant to markedness computation:
- Morpheme count (un-happy = 2, happy = 1)
- Presence of negative prefix (un-, in-, dis-)
- Derivational complexity
-/
structure Morphology where
  /-- The surface form -/
  form : String
  /-- Number of morphemes -/
  morphemeCount : Nat
  /-- Has a negative prefix (un-, in-, dis-, etc.) -/
  hasNegativePrefix : Bool
  /-- Is derived from the antonym (e.g., "unhappy" from "happy") -/
  isDerived : Bool
  deriving Repr, DecidableEq, BEq

/-- Simple morphology for a monomorphemic adjective -/
def simpleMorphology (form : String) : Morphology :=
  { form := form
  , morphemeCount := 1
  , hasNegativePrefix := false
  , isDerived := false
  }

/-- Morphology for a prefixed negative adjective -/
def prefixedMorphology (form : String) (pfx : String := "un") : Morphology :=
  { form := form
  , morphemeCount := 2  -- pfx + base
  , hasNegativePrefix := true
  , isDerived := true
  }

-- ============================================================================
-- PART 2: Extended Adjective Entry
-- ============================================================================

/--
Extended gradable adjective entry with morphological information.

Extends `GradableAdjEntry` with:
- Morphological structure for markedness computation
- Polarity indicator (positive vs negative pole)
-/
structure GradableAdjWithMorphology (max : Nat) extends GradableAdjEntry max where
  /-- Morphological structure -/
  morphology : Morphology
  /-- Is this the positive pole of the scale? -/
  isPositivePole : Bool
  deriving Repr

-- ============================================================================
-- PART 3: Markedness Criteria
-- ============================================================================

/--
A markedness criterion computes which member of an antonym pair is marked.

Given two adjective entries (typically an antonym pair), the criterion
returns the form that is MARKED (more costly, requiring more justification).

Returns `none` if the criterion cannot determine markedness (e.g., both
have equal morphological complexity).
-/
structure MarkednessCriterion where
  /-- Name of this criterion -/
  name : String
  /-- Academic source -/
  citation : String
  /-- Compute which form is marked; returns the marked form -/
  computeMarked : {max : Nat} → GradableAdjWithMorphology max →
                   GradableAdjWithMorphology max → Option String

/--
Morphological complexity criterion.

The form with MORE morphemes is marked.
This captures cases like un-happy > happy.

From Horn (1984): "Toward a new taxonomy for pragmatic inference"
-/
def morphologicalCriterion : MarkednessCriterion where
  name := "Morphological Complexity"
  citation := "Horn (1984)"
  computeMarked := fun adj1 adj2 =>
    if adj1.morphology.morphemeCount > adj2.morphology.morphemeCount then
      some adj1.form
    else if adj2.morphology.morphemeCount > adj1.morphology.morphemeCount then
      some adj2.form
    else
      none  -- Equal complexity, cannot determine

/--
Scale direction criterion.

The NEGATIVE pole is marked.
This captures cases like short (negative pole) vs tall (positive pole).

From Bierwisch (1989), Kennedy (2007)
-/
def scaleDirectionCriterion : MarkednessCriterion where
  name := "Scale Direction"
  citation := "Bierwisch (1989), Kennedy (2007)"
  computeMarked := fun adj1 adj2 =>
    -- Negative pole (isPositivePole = false) is marked
    if adj1.isPositivePole && !adj2.isPositivePole then
      some adj2.form  -- adj2 is negative pole, hence marked
    else if !adj1.isPositivePole && adj2.isPositivePole then
      some adj1.form  -- adj1 is negative pole, hence marked
    else
      none  -- Same polarity, cannot determine

/--
Negative prefix criterion.

Forms with negative prefixes (un-, in-, dis-) are marked.
This is a specific case of morphological complexity that tracks
derivational direction.

From Cruse (1986)
-/
def negativePrefixCriterion : MarkednessCriterion where
  name := "Negative Prefix"
  citation := "Cruse (1986)"
  computeMarked := fun adj1 adj2 =>
    if adj1.morphology.hasNegativePrefix && !adj2.morphology.hasNegativePrefix then
      some adj1.form
    else if adj2.morphology.hasNegativePrefix && !adj1.morphology.hasNegativePrefix then
      some adj2.form
    else
      none

-- ============================================================================
-- PART 4: Combined Markedness Computation
-- ============================================================================

/--
Default priority ordering for markedness criteria.

Following Rett (2015) and Horn (1984):
1. Morphological complexity (most reliable)
2. Negative prefix (specific morphological indicator)
3. Scale direction (fallback for equal morphology)
-/
def defaultCriteria : List MarkednessCriterion :=
  [morphologicalCriterion, negativePrefixCriterion, scaleDirectionCriterion]

/--
Compute markedness using a list of criteria in priority order.

Returns the first successful determination.
-/
def computeMarkedWithCriteria {max : Nat}
    (criteria : List MarkednessCriterion)
    (adj1 adj2 : GradableAdjWithMorphology max) : Option String :=
  criteria.findSome? (·.computeMarked adj1 adj2)

/--
Compute markedness using default criteria.
-/
def computeMarked {max : Nat}
    (adj1 adj2 : GradableAdjWithMorphology max) : Option String :=
  computeMarkedWithCriteria defaultCriteria adj1 adj2

/--
Check if a specific form is the marked one in a pair.
-/
def isMarkedForm {max : Nat}
    (form : String) (adj1 adj2 : GradableAdjWithMorphology max) : Bool :=
  computeMarked adj1 adj2 == some form

-- ============================================================================
-- PART 5: Production Cost
-- ============================================================================

/--
Production cost based on markedness.

Following Horn's Division of Pragmatic Labor:
- Unmarked forms have baseline cost (1)
- Marked forms have higher cost (2)

This cost differential licenses manner implicatures:
using the more costly form when a cheaper equivalent exists
signals something extra.
-/
def productionCost {max : Nat}
    (form : String)
    (adj1 adj2 : GradableAdjWithMorphology max) : ℚ :=
  if isMarkedForm form adj1 adj2 then 2 else 1

/--
Cost difference between marked and unmarked forms.
-/
def costDifference : ℚ := 1

-- ============================================================================
-- PART 6: Sample Entries
-- ============================================================================

/--
"tall" with morphology: simple, positive pole
-/
def tall_with_morphology : GradableAdjWithMorphology 10 where
  toGradableAdjEntry := tall
  morphology := simpleMorphology "tall"
  isPositivePole := true

/--
"short" with morphology: simple, negative pole
-/
def short_with_morphology : GradableAdjWithMorphology 10 where
  toGradableAdjEntry := short
  morphology := simpleMorphology "short"
  isPositivePole := false

/--
"happy" with morphology: simple, positive pole
-/
def happy_with_morphology : GradableAdjWithMorphology 10 where
  toGradableAdjEntry := happy
  morphology := simpleMorphology "happy"
  isPositivePole := true

/--
"unhappy" with morphology: prefixed, negative pole
-/
def unhappy_with_morphology : GradableAdjWithMorphology 10 where
  toGradableAdjEntry := unhappy
  morphology := prefixedMorphology "unhappy"
  isPositivePole := false

-- ============================================================================
-- PART 7: Theorems
-- ============================================================================

/--
Morphological complexity determines markedness: more morphemes = marked.
-/
theorem morphological_determines_markedness :
    morphologicalCriterion.computeMarked happy_with_morphology unhappy_with_morphology =
    some "unhappy" := by native_decide

/--
Scale direction determines markedness for equal morphology pairs.
-/
theorem scale_direction_for_equal_morphology :
    scaleDirectionCriterion.computeMarked tall_with_morphology short_with_morphology =
    some "short" := by native_decide

/--
Default criteria successfully find "short" as marked in tall/short pair.
-/
theorem default_finds_short_marked :
    computeMarked tall_with_morphology short_with_morphology = some "short" := by native_decide

/--
Default criteria successfully find "unhappy" as marked in happy/unhappy pair.
-/
theorem default_finds_unhappy_marked :
    computeMarked happy_with_morphology unhappy_with_morphology = some "unhappy" := by native_decide

/--
Marked form has higher cost than unmarked.
-/
theorem marked_costs_more :
    productionCost "short" tall_with_morphology short_with_morphology >
    productionCost "tall" tall_with_morphology short_with_morphology := by native_decide

-- ============================================================================
-- PART 8: Summary
-- ============================================================================

/-
## Summary: Neo-Gricean Markedness

### Key Types
* `Morphology`: Morphological structure (morpheme count, prefixes, derivation)
* `GradableAdjWithMorphology`: Extended adjective entry with morphology
* `MarkednessCriterion`: Computes which antonym is marked

### Criteria
* `morphologicalCriterion`: More morphemes means marked
* `scaleDirectionCriterion`: Negative pole means marked
* `negativePrefixCriterion`: Has negative prefix (un, in, dis) means marked

### Key Functions
* `computeMarked`: Determine marked form using default criteria
* `isMarkedForm`: Check if a form is marked
* `productionCost`: Cost for producing a form (2 for marked, 1 for unmarked)

### Key Theorems
* `morphological_determines_markedness`: unhappy marked over happy
* `scale_direction_for_equal_morphology`: short marked over tall
* `marked_costs_more`: Marked forms cost more to produce

### Design Principle
Markedness is COMPUTED from objective properties, not stipulated.
This keeps the lexicon theory-neutral.
-/

end NeoGricean.Markedness
