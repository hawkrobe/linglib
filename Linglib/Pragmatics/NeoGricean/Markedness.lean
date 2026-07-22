import Linglib.Semantics.Degree.Adjective
import Linglib.Semantics.Degree.Defs
import Mathlib.Data.Rat.Defs

/-!
# Neo-Gricean markedness and M-alternatives
[horn-1984] [levinson-2000] [rett-2015]

Markedness computation for the M-principle / division of pragmatic
labor ([horn-1984]; [levinson-2000]): which member of an antonym pair
is the *marked* (costlier) form, computed from objective properties
rather than stipulated in the lexicon.

Two distinct markedness notions feed the computation and should not be
conflated: **form markedness** (morphological complexity, negative
prefixation — the notion [horn-1984]'s division of labor ranges over)
and **pole markedness** (the negative pole of a scalar dimension —
[bierwisch-1989]; [kennedy-2007]). The criteria below keep them
separate; `computeMarked` resolves them in a fixed priority order
(morphological complexity, then negative prefix, then scale direction).
The priority ordering is this formalization's resolution policy — the
sources motivate the individual criteria, not the ordering.

M-alternatives ([rett-2015]) differ in form cost, not truth conditions:
they exist only in polar-invariant constructions, where antonyms are
truth-conditionally equivalent (equatives, degree questions) — not in
polar-variant ones (positives, comparatives, measure phrases).

English worked entries (`tall_with_morphology`, …) live in
`Fragments/English/Predicates/Adjectival.lean`; the studies exercising
them are `Studies/Horn1984.lean`, `Studies/Krifka2007.lean`, and
`Studies/Rett2015.lean`.
-/

namespace NeoGricean.Markedness

open Degree

/-- Morphological structure of an adjective form: morpheme count,
negative prefixation, and derivational status. -/
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

/-- Morphology of a monomorphemic adjective. -/
def simpleMorphology (form : String) : Morphology :=
  { form := form
  , morphemeCount := 1
  , hasNegativePrefix := false
  , isDerived := false
  }

/-- Morphology of a negative-prefixed adjective (prefix + base). -/
def prefixedMorphology (form : String) : Morphology :=
  { form := form
  , morphemeCount := 2
  , hasNegativePrefix := true
  , isDerived := true
  }

/-- A gradable adjective entry extended with morphological structure and
scale-pole information, the inputs to markedness computation. -/
structure GradableAdjWithMorphology extends GradableAdjective where
  /-- Morphological structure -/
  morphology : Morphology
  /-- Is this the positive pole of the scale? -/
  isPositivePole : Bool
  deriving Repr

/-- A markedness criterion: given an antonym pair, return the *marked*
(costlier) form, or `none` when the criterion cannot decide. -/
abbrev MarkednessCriterion :=
  GradableAdjWithMorphology → GradableAdjWithMorphology → Option String

/-- Morphological-complexity criterion ([horn-1984]): the form with
more morphemes is marked (un-happy over happy). -/
def morphologicalCriterion : MarkednessCriterion := fun adj1 adj2 =>
  if adj1.morphology.morphemeCount > adj2.morphology.morphemeCount then
    some adj1.form
  else if adj2.morphology.morphemeCount > adj1.morphology.morphemeCount then
    some adj2.form
  else
    none

/-- Negative-prefix criterion ([cruse-1986]): a form with a negative
prefix (un-, in-, dis-) is marked. A special case of morphological
complexity that tracks derivational direction. -/
def negativePrefixCriterion : MarkednessCriterion := fun adj1 adj2 =>
  if adj1.morphology.hasNegativePrefix && !adj2.morphology.hasNegativePrefix then
    some adj1.form
  else if adj2.morphology.hasNegativePrefix && !adj1.morphology.hasNegativePrefix then
    some adj2.form
  else
    none

/-- Scale-direction criterion ([bierwisch-1989]; [kennedy-2007]): the
negative pole is marked (*short* against *tall*). -/
def scaleDirectionCriterion : MarkednessCriterion := fun adj1 adj2 =>
  if adj1.isPositivePole && !adj2.isPositivePole then
    some adj2.form
  else if !adj1.isPositivePole && adj2.isPositivePole then
    some adj1.form
  else
    none

/-- The default criterion priority: morphological complexity, then
negative prefix, then scale direction as the fallback for
morphologically-equal pairs. -/
def defaultCriteria : List MarkednessCriterion :=
  [morphologicalCriterion, negativePrefixCriterion, scaleDirectionCriterion]

/-- Resolve markedness by the first criterion that decides. -/
def computeMarkedWithCriteria
    (criteria : List MarkednessCriterion)
    (adj1 adj2 : GradableAdjWithMorphology) : Option String :=
  criteria.findSome? (· adj1 adj2)

/-- Resolve markedness by the default criteria. -/
def computeMarked
    (adj1 adj2 : GradableAdjWithMorphology) : Option String :=
  computeMarkedWithCriteria defaultCriteria adj1 adj2

/-- Is `form` the marked member of the pair? -/
def isMarkedForm
    (form : String) (adj1 adj2 : GradableAdjWithMorphology) : Bool :=
  computeMarked adj1 adj2 == some form

/-- The marked–unmarked production-cost differential licensing manner
implicatures: using the costlier form when a cheaper equivalent exists
signals something extra ([horn-1984]'s division of pragmatic labor). -/
def costDifference : ℚ := 1

/-- Production cost: baseline 1 for unmarked forms, 1 + `costDifference`
for marked forms. -/
def productionCost
    (form : String)
    (adj1 adj2 : GradableAdjWithMorphology) : ℚ :=
  if isMarkedForm form adj1 adj2 then 1 + costDifference else 1

/-! ### M-alternatives

M-alternatives differ in form cost, not truth conditions, so they exist
only where antonyms are truth-conditionally equivalent: polar-invariant
constructions ([rett-2015]). -/

open Degree (Construction)

/-- Polar variance: whether antonyms differ in truth conditions in a
given construction ("taller than" vs "shorter than") or coincide
("as tall as" vs "as short as"). -/
inductive PolarVariance where
  | variant
  | invariant
  deriving Repr, DecidableEq

/-- Polar variance by adjectival construction ([rett-2015]): positives,
comparatives, and measure phrases are polar-variant; equatives and
degree questions are polar-invariant. -/
def polarVariance : Construction → PolarVariance
  | .positive => .variant
  | .comparative => .variant
  | .equative => .invariant
  | .degreeQuestion => .invariant
  | .measurePhrase => .variant

/-- An M-alternative set: two forms differing in cost but not truth
conditions, in a polar-invariant construction. -/
structure MAlternativeSet where
  /-- The marked (costlier) form -/
  marked : String
  /-- The unmarked (cheaper) form -/
  unmarked : String
  /-- The dimension they share (e.g., .height) -/
  dimension : Features.ScalarDimension
  /-- The cost difference between forms -/
  costDifference : ℚ
  /-- Construction where they're equivalent -/
  construction : Construction
  deriving Repr

instance : BEq MAlternativeSet where
  beq s1 s2 := s1.marked == s2.marked && s1.unmarked == s2.unmarked &&
               s1.dimension == s2.dimension && s1.construction == s2.construction

/-- Generate the M-alternative set for an antonym pair: defined exactly
when the construction is polar-invariant and markedness is decidable
for the pair. -/
def generateMAlternatives (adj1 adj2 : GradableAdjWithMorphology)
    (construction : Construction) : Option MAlternativeSet :=
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
        dimension := adj1.dimension.getD .unspecified
        costDifference := Markedness.costDifference
        construction := construction
      }

/-- Is `form` the marked member of the pair's M-alternative set? -/
def isMarkedInMAlternatives
    (form : String)
    (adj1 adj2 : GradableAdjWithMorphology)
    (construction : Construction) : Bool :=
  match generateMAlternatives adj1 adj2 construction with
  | none => false
  | some mAlt => mAlt.marked == form

/-- The M-alternative of `form` in the pair, if any. -/
def getMAlternative
    (form : String)
    (adj1 adj2 : GradableAdjWithMorphology)
    (construction : Construction) : Option String :=
  match generateMAlternatives adj1 adj2 construction with
  | none => none
  | some mAlt =>
    if mAlt.marked == form then some mAlt.unmarked
    else if mAlt.unmarked == form then some mAlt.marked
    else none

end NeoGricean.Markedness
