/-
# Vagueness: Empirical Data and Theoretical Puzzles

Theory-neutral empirical patterns and formal puzzles for vague predicates.

## Scope

This module covers vagueness-specific phenomena:
- Borderline cases: intermediate judgments for middle values
- Sorites paradox: acceptance of individual premises, rejection of conclusion
- Higher-order vagueness: borderline cases of borderline cases
- Penumbral connections: logical relationships in borderline region
- Tolerance principle: the sorites ingredient

For degree semantics (scale structure, Kennedy typology, degree modifiers),
see `Phenomena/Degrees.lean`.

## Insight

Vagueness arises from degree semantics + threshold uncertainty:
- Degrees provide the underlying scale
- Uncertain thresholds create borderline cases and sorites susceptibility

## Key References

- @cite{fine-1975}
- @cite{williamson-1994}
- @cite{edgington-1997}
- @cite{keefe-2000}
- @cite{lassiter-goodman-2017}
-/

namespace Phenomena.Gradability.Vagueness


/--
Empirical pattern: Borderline cases elicit hedging and uncertainty.

For individuals near the inferred threshold:
- Speakers hedge or refuse to answer
- Judgments show high variance across informants
- Neither "A" nor "not A" feels fully appropriate

Source: @cite{lassiter-goodman-2017} Section 1, @cite{kennedy-2007}
-/
structure BorderlineDatum where
  /-- The adjective -/
  adjective : String
  /-- Description of the context/comparison class -/
  context : String
  /-- Clear positive case (definitely A) -/
  clearPositive : String
  /-- Clear positive value -/
  clearPositiveValue : String
  /-- Clear negative case (definitely not A) -/
  clearNegative : String
  /-- Clear negative value -/
  clearNegativeValue : String
  /-- Borderline case -/
  borderline : String
  /-- Borderline value -/
  borderlineValue : String
  deriving Repr

/-- House price borderline example. -/
def expensiveHouse : BorderlineDatum :=
  { adjective := "expensive"
  , context := "Neighborhood where most houses cost $300,000-$600,000"
  , clearPositive := "Williams' house"
  , clearPositiveValue := "$1,000,000"
  , clearNegative := "Clarks' house"
  , clearNegativeValue := "$75,000"
  , borderline := "Jacobsons' house"
  , borderlineValue := "$475,000"
  }

/-- Height borderline example. -/
def tallPerson : BorderlineDatum :=
  { adjective := "tall"
  , context := "Adult American men (mean ~5'9\", SD ~3\")"
  , clearPositive := "Andre the Giant"
  , clearPositiveValue := "7'4\""
  , clearNegative := "Danny DeVito"
  , clearNegativeValue := "4'10\""
  , borderline := "Average man"
  , borderlineValue := "5'10\""
  }

def borderlineExamples : List BorderlineDatum :=
  [expensiveHouse, tallPerson]


/--
Empirical pattern: The sorites paradox.

Given:
1. A clearly Adj individual (premise 1)
2. A tolerance principle: "If x is Adj and y is ε smaller, then y is Adj" (premise 2)
3. Iterated application leads to a clearly non-Adj individual (conclusion)

Empirical observations:
- People accept premise 1 (the clear case)
- People accept individual instances of premise 2 (each step seems valid)
- People reject the conclusion (the absurd case)
- People show gradient acceptance as cases approach the threshold

Source: @cite{edgington-1997}, @cite{lassiter-goodman-2017} Section 5
-/
structure SoritesDatum where
  adjective : String
  scale : String
  toleranceGap : String
  clearPositive : String
  positiveValue : String
  clearNegative : String
  negativeValue : String
  numSteps : Nat
  acceptPremise1 : Bool
  acceptToleranceSteps : Bool
  acceptConclusion : Bool
  deriving Repr

def tallSorites : SoritesDatum :=
  { adjective := "tall"
  , scale := "height"
  , toleranceGap := "1 mm"
  , clearPositive := "Andre the Giant (7'4\")"
  , positiveValue := "7'4\""
  , clearNegative := "Danny DeVito (4'10\")"
  , negativeValue := "4'10\""
  , numSteps := 762  -- ~30 inches = 762 mm
  , acceptPremise1 := true
  , acceptToleranceSteps := true  -- each individual step accepted
  , acceptConclusion := false     -- paradoxical
  }

def heapSorites : SoritesDatum :=
  { adjective := "heap"
  , scale := "number of grains"
  , toleranceGap := "1 grain"
  , clearPositive := "10,000 grains"
  , positiveValue := "10000"
  , clearNegative := "1 grain"
  , negativeValue := "1"
  , numSteps := 9999
  , acceptPremise1 := true
  , acceptToleranceSteps := true
  , acceptConclusion := false
  }

def expensiveSorites : SoritesDatum :=
  { adjective := "expensive"
  , scale := "price"
  , toleranceGap := "$1"
  , clearPositive := "$10,000,000 house"
  , positiveValue := "10000000"
  , clearNegative := "$1 house"
  , negativeValue := "1"
  , numSteps := 9999999
  , acceptPremise1 := true
  , acceptToleranceSteps := true
  , acceptConclusion := false
  }

def soritesExamples : List SoritesDatum :=
  [tallSorites, heapSorites, expensiveSorites]


/--
The problem of higher-order vagueness.

If "tall" has borderline cases, what about "borderline tall"?
Is there a sharp boundary between "borderline tall" and "clearly tall"?

- First-order vagueness: borderline cases of "tall"
- Second-order vagueness: borderline cases of "borderline tall"
- Third-order vagueness: borderline cases of "borderline borderline tall"
-... and so on

This threatens any theory that posits sharp boundaries anywhere.

Source: @cite{fine-1975}, @cite{williamson-1994},
-/
structure HigherOrderVaguenessData where
  basePredicate : String
  clearlyPositive : String
  borderline : String
  clearlyNegative : String
  sharpClearlyBorderline : Bool
  sharpBorderlineNot : Bool
  iteratesUpward : Bool
  deriving Repr

def tallHigherOrder : HigherOrderVaguenessData :=
  { basePredicate := "tall"
  , clearlyPositive := "7'0\" is clearly tall"
  , borderline := "5'9\" is borderline tall"
  , clearlyNegative := "5'0\" is clearly not tall"
  , sharpClearlyBorderline := false  -- Puzzle: is 6'3\" clearly tall or borderline?
  , sharpBorderlineNot := false      -- Puzzle: is 5'6\" borderline or clearly not?
  , iteratesUpward := true           -- If no sharp boundary, problem repeats
  }

def higherOrderExamples : List HigherOrderVaguenessData := [tallHigherOrder]

/--
The "definitely" operator and higher-order vagueness.

If "Definitely tall" means "clearly tall" (not borderline), then:
- "Definitely tall" should have sharper boundaries than "tall"
- But "definitely" is itself vague.
- So we get: "borderline definitely tall"

Iterating: "definitely definitely tall", etc.

Source: @cite{fine-1975}, @cite{williamson-1994}
-/
structure DefinitelyOperatorData where
  predicate : String
  eliminatesBorderline : Bool
  definitelyIsVague : Bool
  borderlineDefinitely : Bool
  iterationHelps : Bool
  deriving Repr

def definitelyOperator : DefinitelyOperatorData :=
  { predicate := "tall"
  , eliminatesBorderline := true   -- that's the intent
  , definitelyIsVague := true      -- the problem
  , borderlineDefinitely := true   -- so this is possible
  , iterationHelps := false        -- problem just moves up
  }


/--
Penumbral connections: logical relationships that hold even in borderline cases.

Even if we don't know whether John is tall:
- "John is tall ∨ John is not tall" is true (excluded middle)
- "John is tall ∧ John is not tall" is false (non-contradiction)
- If John = 5'9" and Mary = 5'9", then "John is tall ↔ Mary is tall" (same-height)

These are "penumbral truths" - true in the borderline region.

Supervaluationism: true iff true on ALL precisifications.
Degree theories: must explain why these have degree 1.

Source: @cite{fine-1975}, @cite{keefe-2000}
-/
structure PenumbralConnectionData where
  connectionName : String
  formalStatement : String
  alwaysTrue : Bool
  borderlineExample : String
  supervaluationismCaptures : Bool
  degreeTheoryCaptures : Bool
  deriving Repr

def excludedMiddle : PenumbralConnectionData :=
  { connectionName := "Excluded Middle"
  , formalStatement := "∀x. Tall(x) ∨ ¬Tall(x)"
  , alwaysTrue := true
  , borderlineExample := "John is 5'9\". 'John is tall or John is not tall' is true"
  , supervaluationismCaptures := true   -- true on all precisifications
  , degreeTheoryCaptures := false       -- 0.5 ∨ 0.5 = 0.5 ≠ 1 (with standard ∨)
  }

def nonContradiction : PenumbralConnectionData :=
  { connectionName := "Non-Contradiction"
  , formalStatement := "∀x. ¬(Tall(x) ∧ ¬Tall(x))"
  , alwaysTrue := true
  , borderlineExample := "John is 5'9\". 'John is tall and not tall' is false"
  , supervaluationismCaptures := true
  , degreeTheoryCaptures := false  -- 0.5 ∧ 0.5 = 0.5 ≠ 0
  }

def sameHeightConnection : PenumbralConnectionData :=
  { connectionName := "Same-Height Equivalence"
  , formalStatement := "∀x y. Height(x) = Height(y) → (Tall(x) ↔ Tall(y))"
  , alwaysTrue := true
  , borderlineExample := "John and Mary are both 5'9\". 'John is tall iff Mary is tall' is true"
  , supervaluationismCaptures := true  -- all precisifications respect this
  , degreeTheoryCaptures := true       -- same degree → same truth value
  }

def comparativeEntailment : PenumbralConnectionData :=
  { connectionName := "Comparative Entailment"
  , formalStatement := "∀x y. Taller(x, y) ∧ Tall(y) → Tall(x)"
  , alwaysTrue := true
  , borderlineExample := "If 6'0\" John is taller than 5'9\" Mary, and Mary is tall, John is tall"
  , supervaluationismCaptures := true
  , degreeTheoryCaptures := true
  }

def penumbralExamples : List PenumbralConnectionData :=
  [excludedMiddle, nonContradiction, sameHeightConnection, comparativeEntailment]


/--
The tolerance principle: the central ingredient in sorites paradoxes.

Tolerance: If x is F and y differs from x by only a tiny amount,
           then y is also F.

This seems true for vague predicates:
- 1mm can't make the difference between tall and not-tall
- $1 can't make the difference between expensive and not-expensive
- 1 grain can't make the difference between heap and not-heap

But iterated application leads to absurdity (the sorites).

Source: @cite{wright-1976}, @cite{fara-2000}
-/
structure TolerancePrincipleData where
  predicate : String
  scale : String
  toleranceMargin : String
  individualStepAcceptable : Bool
  iterationAbsurd : Bool
  proposedResolution : String
  deriving Repr

def heightTolerance : TolerancePrincipleData :=
  { predicate := "tall"
  , scale := "height"
  , toleranceMargin := "1 mm"
  , individualStepAcceptable := true
  , iterationAbsurd := true
  , proposedResolution := "Various: epistemicism, degree theory, supervaluationism, contextualism"
  }

def priceTolerance : TolerancePrincipleData :=
  { predicate := "expensive"
  , scale := "price"
  , toleranceMargin := "$1"
  , individualStepAcceptable := true
  , iterationAbsurd := true
  , proposedResolution := "Threshold uncertainty makes each step probably but not certainly acceptable"
  }

def toleranceExamples : List TolerancePrincipleData :=
  [heightTolerance, priceTolerance]

/--
Probabilistic sorites analysis.

Each tolerance step is highly probable, not certain.

Let P(step) = 0.99 (each step is 99% acceptable)
After N steps: P(all steps) = 0.99^N

For N = 762 (mm from 7'4\" to 4'10\"):
0.99^762 ≈ 0.0005 (extremely unlikely)

The paradox dissolves: the argument is valid but unsound.
Each premise is probably true, but the conjunction is probably false.

Source: @cite{edgington-1997}, @cite{lassiter-goodman-2017} Section 5
-/
structure ProbabilisticSoritesData where
  predicate : String
  singleStepProbability : Float
  numSteps : Nat
  cumulativeProbability : Float
  premise1Accepted : Bool
  eachStepAccepted : Bool
  fullArgumentAccepted : Bool
  deriving Repr

def tallProbabilisticSorites : ProbabilisticSoritesData :=
  { predicate := "tall"
  , singleStepProbability := 0.99
  , numSteps := 762
  , cumulativeProbability := 0.0005  -- 0.99^762
  , premise1Accepted := true
  , eachStepAccepted := true
  , fullArgumentAccepted := false  -- conjunction fails
  }

def probabilisticSoritesExamples : List ProbabilisticSoritesData :=
  [tallProbabilisticSorites]


/--
Formal constraints that any adequate theory of vagueness should satisfy.

These are theory-neutral desiderata. A theory's success is measured
by how well it accounts for these patterns.

Source: Various
-/
structure VaguenessDesideratum where
  name : String
  description : String
  formalStatement : String
  importance : String
  deriving Repr

def borderlineCasesExist : VaguenessDesideratum :=
  { name := "Borderline Cases"
  , description := "Vague predicates have cases where judgment is uncertain"
  , formalStatement := "∃x. ¬Determinately(P(x)) ∧ ¬Determinately(¬P(x))"
  , importance := "Distinguishes vagueness from mere ignorance"
  }

def toleranceIntuition : VaguenessDesideratum :=
  { name := "Tolerance"
  , description := "Tiny differences can't matter for vague predicates"
  , formalStatement := "∀x y. |x - y| < ε → (P(x) → P(y))"
  , importance := "Captures the phenomenology of vagueness"
  }

def soritesParadoxicality : VaguenessDesideratum :=
  { name := "Sorites Paradoxicality"
  , description := "The sorites is genuinely paradoxical, not just a fallacy"
  , formalStatement := "Premises seem true, argument seems valid, conclusion seems false"
  , importance := "Any resolution must explain why the argument seems compelling"
  }

def penumbralPreservation : VaguenessDesideratum :=
  { name := "Penumbral Preservation"
  , description := "Classical logic holds even in borderline cases"
  , formalStatement := "P ∨ ¬P is true even when P is borderline"
  , importance := "Distinguishes vagueness from ambiguity"
  }

def higherOrderProblem : VaguenessDesideratum :=
  { name := "Higher-Order Vagueness"
  , description := "The boundary of borderline cases is itself vague"
  , formalStatement := "∃x. ¬Det(Borderline(P, x)) ∧ ¬Det(¬Borderline(P, x))"
  , importance := "Sharp boundaries for borderline ≈ sharp boundaries for P"
  }

def desiderata : List VaguenessDesideratum :=
  [borderlineCasesExist, toleranceIntuition, soritesParadoxicality,
   penumbralPreservation, higherOrderProblem]


/--
Interest-relativity of vague extension.

The extension of a vague gradable adjective can change when an agent's
*interests* change, even if the precise measured property stays constant.
This is evidence that the degrees of vague quantities incorporate
information about interests, not just objective measurements.

Source: @cite{fara-2000}, @cite{dinis-jacinto-2026} §5.3
-/
structure InterestRelativityDatum where
  adjective : String
  individual : String
  preciseProperty : String
  preciseValueUnchanged : Bool
  interestsChanged : String
  extensionBefore : Bool
  extensionAfter : Bool
  extensionFlipped : Bool
  deriving Repr

/-- Prince William / Charles III: as William ages, his interests shift
    toward considering people with m hairs bald whom he previously didn't.
    Charles III has the same number of hairs, but was bald∅ before and
    isn't now — his baldness *degree* changed because degrees partially
    reflect interests. -/
def charlesIIIBaldness : InterestRelativityDatum :=
  { adjective := "bald"
  , individual := "Charles III"
  , preciseProperty := "hair count"
  , preciseValueUnchanged := true
  , interestsChanged := "Prince William's interests shifted: previously considered m hairs not-bald, now considers m hairs bald"
  , extensionBefore := true   -- was bald∅ at earlier context
  , extensionAfter := false   -- no longer bald∅ at later context
  , extensionFlipped := true  -- extension changed despite same hair count
  }

/-- Context-dependent expensiveness: same price, different interests. -/
def houseExpensiveness : InterestRelativityDatum :=
  { adjective := "expensive"
  , individual := "$475,000 house"
  , preciseProperty := "price"
  , preciseValueUnchanged := true
  , interestsChanged := "Buyer's budget increased from $400k to $600k"
  , extensionBefore := true
  , extensionAfter := false
  , extensionFlipped := true
  }

def interestRelativityExamples : List InterestRelativityDatum :=
  [charlesIIIBaldness, houseExpensiveness]


/--
Tolerance step non-uniformity.

Not all tolerance steps feel equally acceptable. In a Soritical sequence
where adjacent elements differ by one precise unit (one hair, one mm,
one dollar), some steps feel like negligible differences and others feel
like significant jumps — even though the precise difference is identical.

This is evidence that the *vague* difference between adjacent elements
is not a simple function of the *precise* difference.

Source: @cite{fara-2000} on salient similarity, @cite{dinis-jacinto-2026} §6.1
-/
structure ToleranceStepDatum where
  adjective : String
  preciseDifference : String
  /-- Steps near clear cases feel negligible -/
  clearRegionAcceptance : String
  /-- Steps near the threshold feel significant -/
  thresholdRegionAcceptance : String
  /-- Same precise difference, different perceived significance -/
  nonUniform : Bool
  deriving Repr

/-- Baldness tolerance: removing one hair from someone with 100,000 hairs
    feels negligible; removing one hair from someone near the "boundary"
    can feel significant. -/
def baldnessToleranceSteps : ToleranceStepDatum :=
  { adjective := "bald"
  , preciseDifference := "1 hair"
  , clearRegionAcceptance := "Removing 1 hair from 100,000: clearly still not bald"
  , thresholdRegionAcceptance := "Removing 1 hair near the boundary: judgment uncertain, step feels more significant"
  , nonUniform := true
  }

/-- Height tolerance: 1mm difference between two clearly tall people
    feels negligible; 1mm difference near the threshold feels more
    significant. -/
def heightToleranceSteps : ToleranceStepDatum :=
  { adjective := "tall"
  , preciseDifference := "1 mm"
  , clearRegionAcceptance := "1mm less than 7'0\": still clearly tall"
  , thresholdRegionAcceptance := "1mm less than 5'9\" threshold: judgment shifts more"
  , nonUniform := true
  }

def toleranceStepExamples : List ToleranceStepDatum :=
  [baldnessToleranceSteps, heightToleranceSteps]

/--
Borderline contradiction acceptance.

Experimental data on whether subjects accept sentences of the form
"X is P and not P" (contradictions) and "X is neither P nor not P"
(gaps) for borderline cases of vague predicates.

Key finding: acceptance rates for both contradictions and gaps are
significantly higher for borderline cases than for clear cases.
This is evidence against both classical logic (which rejects all
contradictions) and standard supervaluationism (which makes
contradictions super-false even for borderline cases).

The data is compatible with the TCS framework (@cite{cobreros-etal-2012}),
which predicts that borderline cases tolerantly satisfy P ∧ ¬P.

Source: @cite{alxatib-pelletier-2011}, @cite{ripley-2011},
@cite{serchuk-hargreaves-zach-2011}
-/
structure BorderlineContradictionDatum where
  /-- Study identifier -/
  study : String
  /-- The vague predicate tested -/
  predicate : String
  /-- Stimulus type (visual, scenario-based, etc.) -/
  stimulusType : String
  /-- Description of the borderline case -/
  borderlineCase : String
  /-- Acceptance rate for "X is P and not P" (contradiction) -/
  contradictionAcceptance : Option Float
  /-- Acceptance rate for "X is neither P nor not P" (gap) -/
  gapAcceptance : Option Float
  /-- Whether rates are significantly higher for borderline than clear cases -/
  borderlinePeaks : Bool
  deriving Repr

/-- @cite{alxatib-pelletier-2011}: 5 men of different heights (visual).
    Man #2 (5'11", median size) shows peak contradiction/gap acceptance. -/
def alxatibPelletier2011Tall : BorderlineContradictionDatum :=
  { study := "Alxatib & Pelletier 2011"
  , predicate := "tall"
  , stimulusType := "visual (picture of 5 men with labeled heights)"
  , borderlineCase := "Man #2 (5'11\", median height in display)"
  , contradictionAcceptance := some 44.7  -- "both tall and not tall"
  , gapAcceptance := some 53.9  -- "neither tall nor not tall"
  , borderlinePeaks := true  -- significantly higher than for extreme cases
  }

/-- @cite{ripley-2011}: 7 pairs (A-G) of decreasing nearness (visual).
    Pair C (median distance) shows peak contradiction acceptance. -/
def ripley2011Near : BorderlineContradictionDatum :=
  { study := "Ripley 2011"
  , predicate := "near"
  , stimulusType := "visual (square and circle at varying distances)"
  , borderlineCase := "Pair C (median distance between clear-near A and clear-not-near G)"
  , contradictionAcceptance := none  -- reported as significant but no single percentage
  , gapAcceptance := none
  , borderlinePeaks := true  -- agreement peaks at intermediate pairs
  }

/-- @cite{serchuk-hargreaves-zach-2011}: scenario-based (Susan's wealth).
    Forced-choice with 6 options including "Both", "Neither", "Partially True". -/
def serchukEtAl2011Rich : BorderlineContradictionDatum :=
  { study := "Serchuk, Hargreaves & Zach 2011"
  , predicate := "rich"
  , stimulusType := "scenario (Susan described as between clearly rich and clearly non-rich women)"
  , borderlineCase := "Susan (described as income-wise between clear groups)"
  , contradictionAcceptance := some 19.0  -- "Susan is rich and not rich" judged True
  , gapAcceptance := none
  , borderlinePeaks := true  -- contradiction sentence: 55% False, 19% True, rest other options
  }

def borderlineContradictionData : List BorderlineContradictionDatum :=
  [alxatibPelletier2011Tall, ripley2011Near, serchukEtAl2011Rich]

/-- All three studies find borderline-peaking: contradiction/gap acceptance
    is significantly higher for borderline cases than for clear cases.
    This is the key empirical finding that TCS accounts for and
    standard supervaluationism does not. -/
theorem all_borderline_peak : borderlineContradictionData.all
    (fun d => d.borderlinePeaks) = true := by decide

end Phenomena.Gradability.Vagueness
