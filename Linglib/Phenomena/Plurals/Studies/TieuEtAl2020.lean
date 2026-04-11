import Linglib.Phenomena.Plurals.Multiplicity
import Linglib.Phenomena.ScalarImplicatures.Basic
import Linglib.Theories.Semantics.Alternatives.Lexical

/-!
# Tieu, Bill, Romoli & Crain (2020) @cite{tieu-etal-2020}

Testing theories of plural meanings. *Cognition* 205, 104307.

Three experiments comparing adults' and children's interpretations of
bare plurals in upward- and downward-entailing environments. The results
support an implicature approach to multiplicity inferences: children
compute fewer multiplicity inferences than adults, in parallel with their
behavior on standard scalar implicatures, and the two inference types
are correlated within children.

## Core Argument

The paper adjudicates between three theories of why "Emily fed giraffes"
means "more than one":

1. **Ambiguity**: plural is polysemous (inclusive/exclusive), Strongest
   Meaning Hypothesis selects the stronger reading.
2. **Implicature**: plural literally means "one or more," the "more than
   one" inference is a scalar implicature with the singular as alternative.
3. **Homogeneity**: multiplicity arises from homogeneity presupposition.

Key discriminating prediction (Uniformity Prediction): if multiplicity
inferences are scalar implicatures, children should compute fewer of both,
and rates should be correlated.

## Connection to Linglib

- Imports `Multiplicity` data for the monotonicity pattern
- Imports `HornScale` for the singular/plural scale
- Links multiplicity inferences to `ScalarImplicatures/Basic` DE blocking
-/

namespace Phenomena.Plurals.Studies.TieuEtAl2020

open Alternatives (Monotonicity)
open Alternatives.Number (NumberExpr numberScale)
open Phenomena.Plurals.Multiplicity (PluralTheory MonotonicityParallel
  implicature_uniquely_predicts)


-- Experimental Design

/--
A truth-value judgment trial: participant sees a story where the character
acts on one object from a set, then judges a bare plural test sentence.
-/
structure TVJTrial where
  /-- Story context -/
  story : String
  /-- Test sentence -/
  sentence : String
  /-- Polarity of test sentence -/
  polarity : Core.Polarity
  /-- Does accepting the sentence indicate computing multiplicity? -/
  acceptanceIndicatesMultiplicity : Bool
  deriving Repr

/-- Experiment 1: upward-entailing (positive) trial. -/
def exp1_positive : TVJTrial :=
  { story := "Emily has an apple. She feeds one pig. Only that pig was fed."
  , sentence := "Emily fed pigs"
  , polarity := .positive
  , acceptanceIndicatesMultiplicity := false
  -- Rejecting = computing multiplicity (one pig ≠ "more than one")
  }

/-- Experiment 1: downward-entailing (negative) trial. -/
def exp1_negative : TVJTrial :=
  { story := "Emily has food for one giraffe. She feeds that giraffe. The others go unfed."
  , sentence := "Emily didn't feed giraffes"
  , polarity := .negative
  , acceptanceIndicatesMultiplicity := true
  -- Accepting = computing multiplicity locally under negation
  -- (interpreting as: "Emily didn't feed more than one giraffe")
  }


-- Experimental Results

/--
Inference rate for a group in a condition.
-/
structure InferenceRate where
  /-- Which group -/
  group : String
  /-- Inference type -/
  inferenceType : String
  /-- Polarity of context -/
  polarity : Core.Polarity
  /-- Rate of inference-consistent responses (qualitative) -/
  rate : String
  deriving Repr

/-- Experiment 1 key results (qualitative — no exact numbers cited). -/
def exp1Results : List InferenceRate :=
  [ { group := "Adults", inferenceType := "multiplicity"
    , polarity := .positive, rate := "high" }
  , { group := "Adults", inferenceType := "multiplicity"
    , polarity := .negative, rate := "moderate" }
  , { group := "Children", inferenceType := "multiplicity"
    , polarity := .positive, rate := "low" }
  , { group := "Children", inferenceType := "multiplicity"
    , polarity := .negative, rate := "low" }
  ]

/-- Experiment 2 key results (qualitative). -/
def exp2Results : List InferenceRate :=
  [ { group := "Adults", inferenceType := "multiplicity"
    , polarity := .positive, rate := "high" }
  , { group := "Children", inferenceType := "multiplicity"
    , polarity := .positive, rate := "low" }
  , { group := "Adults", inferenceType := "scalar (some)"
    , polarity := .positive, rate := "high" }
  , { group := "Children", inferenceType := "scalar (some)"
    , polarity := .positive, rate := "low" }
  ]


-- Theoretical Analysis

/--
The Uniformity Prediction: if multiplicity inferences are scalar
implicatures, then the between-group pattern (children < adults)
should be the same for both inference types.

The paper confirms this prediction and additionally finds that
children's rates on the two types are significantly correlated.
-/
structure UniformityResult where
  /-- Do children compute fewer multiplicity inferences than adults? -/
  childrenFewerMultiplicity : Bool
  /-- Do children compute fewer scalar implicatures than adults? -/
  childrenFewerSI : Bool
  /-- Are the two rates correlated within children? -/
  correlatedInChildren : Bool
  deriving Repr

def uniformityConfirmed : UniformityResult :=
  { childrenFewerMultiplicity := true
  , childrenFewerSI := true
  , correlatedInChildren := true
  }

/-- All three components of the Uniformity Prediction are confirmed. -/
theorem uniformity_all_confirmed :
    uniformityConfirmed.childrenFewerMultiplicity = true ∧
    uniformityConfirmed.childrenFewerSI = true ∧
    uniformityConfirmed.correlatedInChildren = true :=
  ⟨rfl, rfl, rfl⟩


-- Connection to Horn Scale Infrastructure

/-- The singular/plural scale predicts multiplicity as a scalar implicature:
    using the plural (weaker) implicates the negation of the singular (stronger). -/
theorem plural_has_singular_alternative :
    Alternatives.strongerAlternatives numberScale .plural = [.singular] := by
  decide

/-- In DE contexts, the scale reverses (weaker alternatives are relevant),
    so the multiplicity inference does not arise. -/
theorem de_context_no_multiplicity :
    Alternatives.scalarAlternativesInContext numberScale .plural .downward = [] := by
  decide

/-- In UE contexts, the singular is the relevant alternative,
    producing the multiplicity inference. -/
theorem ue_context_multiplicity :
    Alternatives.scalarAlternativesInContext numberScale .plural .upward = [.singular] := by
  decide


-- Cross-reference to Multiplicity data

/-- The paper's findings match the monotonicity pattern in the data file:
    multiplicity arises in UE (positive) but not DE (negative). -/
theorem consistent_with_monotonicity_data :
    Phenomena.Plurals.Multiplicity.fedGiraffes.multiplicityInPositive = true ∧
    Phenomena.Plurals.Multiplicity.fedGiraffes.multiplicityInNegative = false := by
  exact ⟨rfl, rfl⟩

/-- The implicature approach is uniquely identified by any of the three
    findings. Here we use `predictsChildrenComputeFewer`: any theory
    predicting children compute fewer must use the SI mechanism. -/
theorem implicature_uniquely_supported (t : PluralTheory)
    (h : t.usesSIMechanism = true) :
    t = .implicature :=
  Phenomena.Plurals.Multiplicity.implicature_uniquely_predicts t h


-- Experiment 3: Singular contexts (adults-only, ternary judgment)

/--
Experiment 3 uses a ternary judgment task (small/medium/large strawberry
for false/neither/true) with adults on Amazon Mechanical Turk.

In singular contexts (one object acted upon), the three theories
predict different status for positive vs negative plural sentences:
- "Koala bought pears" (only bought one) — literally true but misleading
- "Koala didn't buy pears" (only bought one) — literally false

Result: adults gave intermediate reward for positive, minimal for negative,
confirming the implicature approach's prediction that they differ in status.
-/
structure TernaryJudgment where
  /-- Test sentence -/
  sentence : String
  /-- Polarity -/
  polarity : Core.Polarity
  /-- Preferred reward level (qualitative) -/
  preferredReward : String
  deriving Repr

def exp3_positive_plural : TernaryJudgment :=
  { sentence := "Koala bought pears"
  , polarity := .positive
  , preferredReward := "intermediate"
  -- Literally true (bought one or more), but false implicature
  }

def exp3_negative_plural : TernaryJudgment :=
  { sentence := "Koala didn't buy pears"
  , polarity := .negative
  , preferredReward := "minimal"
  -- Literally false (Koala did buy one or more pears)
  }

/-- Adults assign different status to positive vs negative in singular contexts.
    This confirms the implicature approach's singular context prediction. -/
theorem exp3_confirms_asymmetry :
    exp3_positive_plural.preferredReward ≠ exp3_negative_plural.preferredReward := by
  decide

/-- The singular context finding matches the implicature theory's prediction:
    the implicature account uniquely predicts positive/negative asymmetry. -/
theorem exp3_matches_implicature_prediction (t : PluralTheory)
    (h : t.positiveNegativeDiffer = true) :
    t = .implicature :=
  Phenomena.Plurals.Multiplicity.implicature_uniquely_discriminates_singular t h


-- Cross-directory bridge: Multiplicity parallels scalar implicatures

/-- The multiplicity inference exhibits DE blocking — the same pattern as
    classical scalar implicatures documented in ScalarImplicatures/Basic.lean.

    Specifically: the some/all DE blocking datum shows implicatures arise in UE
    but not DE, exactly paralleling the multiplicity pattern. -/
theorem multiplicity_parallels_si_de_blocking :
    Phenomena.ScalarImplicatures.someAllBlocking.implicatureInUE = true ∧
    Phenomena.ScalarImplicatures.someAllBlocking.implicatureInDE = false ∧
    Phenomena.Plurals.Multiplicity.fedGiraffes.multiplicityInPositive = true ∧
    Phenomena.Plurals.Multiplicity.fedGiraffes.multiplicityInNegative = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Both the number scale and the quantifier scale predict the same
    pattern: stronger alternatives in UE, none/weaker in DE. -/
theorem scales_predict_same_pattern :
    (Alternatives.scalarAlternativesInContext numberScale .plural .upward).length > 0 ∧
    (Alternatives.scalarAlternativesInContext numberScale .plural .downward).length = 0 ∧
    (Alternatives.scalarAlternativesInContext
      Alternatives.Quantifiers.quantScale .some_ .upward).length > 0 := by
  decide

end Phenomena.Plurals.Studies.TieuEtAl2020
