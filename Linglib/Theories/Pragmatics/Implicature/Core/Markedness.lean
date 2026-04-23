/-
# Neo-Gricean Markedness Infrastructure

Formalization of markedness computation for @cite{rett-2015} Chapters 5-6.

## Insight

Markedness is COMPUTED from objective properties, not stipulated in the lexicon.
This module provides the Implicature-internal machinery for determining which
member of an antonym pair is marked.

## Markedness Criteria

Following @cite{horn-1984} and @cite{rett-2015}:

1. **Morphological complexity**: un-happy > happy (more morphemes = marked)
2. **Scale direction**: negative pole is typically marked
3. **Distributional asymmetry**: marked forms are more restricted

The key point: these are objective, measurable properties. Different theories
(Implicature vs. RSA) can use different mechanisms to derive the same effects.

-/

import Linglib.Theories.Semantics.Gradability.Theory
import Linglib.Fragments.English.Predicates.Adjectival
import Mathlib.Data.Rat.Defs

namespace Implicature.Markedness

open Semantics.Gradability
open Core.Scale (Degree Threshold Degree.toNat Threshold.toNat deg thr)
open Semantics.Gradability (ThresholdPair)
open Features (NegationType)
open Fragments.English.Predicates.Adjectival (tall short happy unhappy)


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
  deriving Repr, DecidableEq

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


/--
Extended gradable adjective entry with morphological information.

Extends `GradableAdjEntry` with:
- Morphological structure for markedness computation
- Polarity indicator (positive vs negative pole)
-/
structure GradableAdjWithMorphology extends GradableAdjEntry where
  /-- Morphological structure -/
  morphology : Morphology
  /-- Is this the positive pole of the scale? -/
  isPositivePole : Bool
  deriving Repr


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
  computeMarked : GradableAdjWithMorphology →
                   GradableAdjWithMorphology → Option String

/--
Morphological complexity criterion.

The form with MORE morphemes is marked.
This captures cases like un-happy > happy.

From @cite{horn-1984}: "Toward a new taxonomy for pragmatic inference"
-/
def morphologicalCriterion : MarkednessCriterion where
  name := "Morphological Complexity"
  citation := "Horn (1984)"
  computeMarked := λ adj1 adj2 =>
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

From @cite{bierwisch-1989}, @cite{kennedy-2007}
-/
def scaleDirectionCriterion : MarkednessCriterion where
  name := "Scale Direction"
  citation := "Bierwisch (1989), Kennedy (2007)"
  computeMarked := λ adj1 adj2 =>
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

From @cite{cruse-1986}
-/
def negativePrefixCriterion : MarkednessCriterion where
  name := "Negative Prefix"
  citation := "Cruse (1986)"
  computeMarked := λ adj1 adj2 =>
    if adj1.morphology.hasNegativePrefix && !adj2.morphology.hasNegativePrefix then
      some adj1.form
    else if adj2.morphology.hasNegativePrefix && !adj1.morphology.hasNegativePrefix then
      some adj2.form
    else
      none


/--
Default priority ordering for markedness criteria.

Following @cite{rett-2015} and @cite{horn-1984}:
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
def computeMarkedWithCriteria
    (criteria : List MarkednessCriterion)
    (adj1 adj2 : GradableAdjWithMorphology) : Option String :=
  criteria.findSome? (·.computeMarked adj1 adj2)

/--
Compute markedness using default criteria.
-/
def computeMarked
    (adj1 adj2 : GradableAdjWithMorphology) : Option String :=
  computeMarkedWithCriteria defaultCriteria adj1 adj2

/--
Check if a specific form is the marked one in a pair.
-/
def isMarkedForm
    (form : String) (adj1 adj2 : GradableAdjWithMorphology) : Bool :=
  computeMarked adj1 adj2 == some form


/--
Production cost based on markedness.

Following Horn's Division of Pragmatic Labor:
- Unmarked forms have baseline cost (1)
- Marked forms have higher cost (2)

This cost differential licenses manner implicatures:
using the more costly form when a cheaper equivalent exists
signals something extra.
-/
def productionCost
    (form : String)
    (adj1 adj2 : GradableAdjWithMorphology) : ℚ :=
  if isMarkedForm form adj1 adj2 then 2 else 1

/--
Cost difference between marked and unmarked forms.
-/
def costDifference : ℚ := 1


/--
"tall" with morphology: simple, positive pole
-/
def tall_with_morphology : GradableAdjWithMorphology where
  toGradableAdjEntry := tall
  morphology := simpleMorphology "tall"
  isPositivePole := true

/--
"short" with morphology: simple, negative pole
-/
def short_with_morphology : GradableAdjWithMorphology where
  toGradableAdjEntry := short
  morphology := simpleMorphology "short"
  isPositivePole := false

/--
"happy" with morphology: simple, positive pole
-/
def happy_with_morphology : GradableAdjWithMorphology where
  toGradableAdjEntry := happy
  morphology := simpleMorphology "happy"
  isPositivePole := true

/--
"unhappy" with morphology: prefixed, negative pole
-/
def unhappy_with_morphology : GradableAdjWithMorphology where
  toGradableAdjEntry := unhappy
  morphology := prefixedMorphology "unhappy"
  isPositivePole := false


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


/-
## Summary: Neo-Gricean Markedness

### Key Types
* `Morphology`: Morphological structure (morpheme count, prefixes, derivation)
* `GradableAdjWithMorphology`: Extended adjective entry with morphology
* `MarkednessCriterion`: Computes which antonym is marked

### Criteria
* `morphologicalCriterion`: More morphemes means marked
* `scaleDirectionCriterion`: Negative pole means marked
* `negativePrefixCriterion`: Has negative prefix (un, dis) means marked

### Key Functions
* `computeMarked`: Determine marked form using default criteria
* `isMarkedForm`: Check if a form is marked
* `productionCost`: Cost for producing a form (2 for marked, 1 for unmarked)

### Theorems
* `morphological_determines_markedness`: unhappy marked over happy
* `scale_direction_for_equal_morphology`: short marked over tall
* `marked_costs_more`: Marked forms cost more to produce

### Design Principle
Markedness is COMPUTED from objective properties, not stipulated.
This keeps the lexicon theory-neutral.
-/

-- ============================================================
-- M-Alternatives (Manner Alternatives)
-- ============================================================

/-! ## M-Alternatives

M-alternatives differ in FORM COST (markedness), not truth conditions.
They only exist in polar-invariant constructions where antonyms have
the same truth conditions (@cite{rett-2015} Chapter 5).

### Polar Variance

Whether antonyms have the same truth conditions depends on the construction:
- Polar-VARIANT: "taller than" ≠ "shorter than" → no M-alternatives
- Polar-INVARIANT: "as tall as" = "as short as" → M-alternatives exist
-/

open Semantics.Degree (AdjectivalConstruction)

/-- Polar variance: do antonyms have the same truth conditions in this construction? -/
inductive PolarVariance where
  | variant    -- Different truth conditions (comparatives, positives)
  | invariant  -- Same truth conditions (equatives, questions)
  deriving Repr, DecidableEq

/-- Polar variance by adjectival construction type.
    @cite{rett-2015} Table 3.1/5.1. -/
def polarVariance : AdjectivalConstruction → PolarVariance
  | .positive => .variant
  | .comparative => .variant
  | .equative => .invariant
  | .degreeQuestion => .invariant
  | .measurePhrase => .variant

/-- An M-alternative set: forms differing in cost but not truth conditions. -/
structure MAlternativeSet where
  /-- The marked (costlier) form -/
  marked : String
  /-- The unmarked (cheaper) form -/
  unmarked : String
  /-- The dimension they share (e.g., .height) -/
  dimension : Features.Dimension
  /-- The cost difference between forms -/
  costDifference : ℚ
  /-- Construction where they're equivalent -/
  construction : AdjectivalConstruction
  deriving Repr

instance : BEq MAlternativeSet where
  beq s1 s2 := s1.marked == s2.marked && s1.unmarked == s2.unmarked &&
               s1.dimension == s2.dimension && s1.construction == s2.construction

/-- Generate M-alternatives from an antonym pair.

    M-alternatives are generated when:
    1. The construction is polar-invariant (antonyms semantically equivalent)
    2. Markedness can be determined for the pair -/
def generateMAlternatives (adj1 adj2 : GradableAdjWithMorphology)
    (construction : AdjectivalConstruction) : Option MAlternativeSet :=
  if polarVariance construction != .invariant then
    none
  else
    match computeMarked adj1 adj2 with
    | none => none
    | some markedForm =>
      let unmarkedForm := if markedForm == adj1.form then adj2.form else adj1.form
      some {
        marked := markedForm
        unmarked := unmarkedForm
        dimension := adj1.dimension
        costDifference := Markedness.costDifference
        construction := construction
      }

/-- Check if a form is the marked member of an M-alternative pair. -/
def isMarkedInMAlternatives
    (form : String)
    (adj1 adj2 : GradableAdjWithMorphology)
    (construction : AdjectivalConstruction) : Bool :=
  match generateMAlternatives adj1 adj2 construction with
  | none => false
  | some mAlt => mAlt.marked == form

/-- Get the M-alternative for a form (if any). -/
def getMAlternative
    (form : String)
    (adj1 adj2 : GradableAdjWithMorphology)
    (construction : AdjectivalConstruction) : Option String :=
  match generateMAlternatives adj1 adj2 construction with
  | none => none
  | some mAlt =>
    if mAlt.marked == form then some mAlt.unmarked
    else if mAlt.unmarked == form then some mAlt.marked
    else none

end Implicature.Markedness
