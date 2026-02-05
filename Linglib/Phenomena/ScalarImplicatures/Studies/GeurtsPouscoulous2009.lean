/-
# Geurts & Pouscoulous (2009) Experimental Data

Experimental data on scalar implicature rates from:
Geurts, B. & Pouscoulous, N. (2009). Embedded implicatures?!
Semantics and Pragmatics, 2(4), 1-34.

## Main Question

Do scalar implicatures arise "locally" inside embedded clauses?

Conventionalists (Chierchia, Levinson, Landman) claim SIs occur
"systematically and freely in arbitrarily embedded positions."

Griceans claim SIs are global pragmatic inferences, not local.

## Four Experiments

1. **Exp 1a-b**: SI rates vary by embedding type (think: 57%, all: 27%, must: 3%)
2. **Exp 2**: Inference task (62%) vs verification task (34%) for simple sentences
3. **Exp 3**: Verification vs inference by monotonicity (UE vs DE)
4. **Exp 4**: Ambiguity detection (70% for genuine, 6% for alleged SI-ambiguities)

## Findings

- Local SIs are not the default in embedded positions
- The inference task biases toward seeing SIs (methodological concern)
- Apparent "local" SIs under belief verbs explained by global SI + competence
- Data strongly favor Gricean over conventionalist accounts
-/

import Mathlib.Data.Rat.Defs
import Linglib.Phenomena.Core.EmpiricalData

namespace Phenomena.ScalarImplicatures.Studies.GeurtsPouscoulous2009

open Phenomena


/-- Citation for this study -/
def citation : String := "Geurts, B. & Pouscoulous, N. (2009). Embedded implicatures?! Semantics and Pragmatics, 2(4), 1-34."

/-- Experiment 2 inference task: "Does X imply Y?" -/
def exp2InferenceMeasure : MeasureSpec :=
  { scale := .proportion, task := .inferenceEndorsement, unit := "percentage 0-100" }

/-- Experiment 2/3 verification task: "Is this true of the picture?" -/
def verificationMeasure : MeasureSpec :=
  { scale := .proportion, task := .truthValueJudgment, unit := "percentage 0-100" }



/--
The two experimental tasks used to probe scalar inferences.
-/
inductive TaskType where
  | inference     -- "Does 'Some B's are in the box' imply 'not all B's'?"
  | verification  -- "Does 'Some B's are in the box' correctly describe [picture]?"
  deriving DecidableEq, BEq, Repr

/--
Stimulus type in the experiment.
-/
structure Stimulus where
  /-- The sentence presented -/
  sentence : String
  /-- The scalar term in the sentence -/
  scalarTerm : String
  /-- For verification: description of the visual stimulus -/
  visualDescription : Option String
  deriving Repr

/--
The critical stimulus used in Experiment 2.
-/
def criticalStimulus : Stimulus :=
  { sentence := "Some of the B's are in the box on the left"
  , scalarTerm := "some"
  , visualDescription := some "All B's in left box, all A's in middle, all C's in right"
  }


/--
Types of embedding contexts tested in Experiment 1a-b.
-/
inductive EmbeddingType where
  | simple   -- "Fred heard some of the Verdi operas"
  | think    -- "Betty thinks Fred heard some..."
  | want     -- "Betty wants Fred to hear some..."
  | must     -- "Fred has to hear some..."
  | all      -- "All students heard some..."
  deriving DecidableEq, BEq, Repr

/--
Monotonicity of the embedding context.
-/
inductive Monotonicity where
  | upwardEntailing    -- UE: all, more than one
  | downwardEntailing  -- DE: not all, not more than one
  | nonMonotonic       -- NM: exactly two
  deriving DecidableEq, BEq, Repr

/--
Result from Experiment 1 by embedding type.

Local SI rates vary dramatically by embedding type,
contrary to conventionalist predictions of systematic local SIs.
-/
structure EmbeddingResult where
  /-- The embedding context -/
  embedding : EmbeddingType
  /-- Rate of local SI (percentage) -/
  localSIRate : Nat
  /-- Sample size -/
  n : Nat
  deriving Repr

/--
Experiment 1a results (n=30).
-/
def exp1aResults : List EmbeddingResult :=
  [ { embedding := .simple, localSIRate := 93, n := 30 }
  , { embedding := .think,  localSIRate := 50, n := 30 }
  , { embedding := .all,    localSIRate := 27, n := 30 }
  , { embedding := .must,   localSIRate := 3,  n := 30 }
  ]

/--
Experiment 1b results (n=31).
-/
def exp1bResults : List EmbeddingResult :=
  [ { embedding := .simple, localSIRate := 94, n := 31 }
  , { embedding := .think,  localSIRate := 65, n := 31 }
  , { embedding := .want,   localSIRate := 32, n := 31 }
  ]

/--
Combined results across both experiments.
-/
def combinedEmbeddingResults : List (EmbeddingType × Nat) :=
  [ (.simple, 93)  -- average of 93 and 94
  , (.think, 57)   -- average of 50 and 65
  , (.all, 27)
  , (.must, 3)
  , (.want, 32)
  ]

/--
Simple sentences show 93% SI rate.
-/
def simpleRate : Nat := 93

/--
Must embedding shows only 3% SI rate.
-/
def mustRate : Nat := 3

/--
Think embedding shows 57% SI rate (avg of 50% and 65%).
-/
def thinkRate : Nat := 57

/--
Simple sentences show high SI rates.
-/
theorem simple_high_rate : simpleRate > 90 := by native_decide

/--
Must embedding nearly eliminates local SIs.

Deontic must shows only 3% local SIs.
-/
theorem must_near_zero : mustRate < 5 := by native_decide

/--
Huge variation by embedding type.

The range from 3% (must) to 93% (simple) refutes the claim
that SIs occur "systematically and freely" in embedded positions.
-/
theorem embedding_variation : simpleRate - mustRate > 85 := by native_decide


/--
Result from a single experimental condition.
-/
structure ConditionResult where
  /-- The task type -/
  task : TaskType
  /-- Rate of scalar inference (as percentage 0-100) -/
  scalarInferenceRate : Nat
  /-- Sample size -/
  n : Nat
  deriving Repr

/--
Inference task result: 62% derived the scalar inference.
When asked "Does this imply not all?", 62% said yes.
-/
def inferenceTaskResult : ConditionResult :=
  { task := .inference
  , scalarInferenceRate := 62
  , n := 32  -- Approximate from paper
  }

/--
Verification task result: 34% derived the scalar inference.
When asked "Does this correctly describe the picture?", 34% said no
(implying they derived the scalar inference and judged it false).
-/
def verificationTaskResult : ConditionResult :=
  { task := .verification
  , scalarInferenceRate := 34
  , n := 32  -- Approximate from paper
  }

/--
Control items in verification task: 97% correct.
This rules out a general "yes" bias.
-/
def controlAccuracy : Nat := 97


/--
Quantifier types tested in Experiment 3.
-/
inductive QuantifierContext where
  | all              -- UE: "All the squares are connected..."
  | moreThanOne      -- UE: "More than one square is connected..."
  | exactlyTwo       -- NM: "Exactly two squares are connected..."
  | notAll           -- DE: "Not all squares are connected..."
  | notMoreThanOne   -- DE: "Not more than one square is connected..."
  deriving DecidableEq, BEq, Repr

/--
Monotonicity of a quantifier context.
-/
def quantifierMonotonicity : QuantifierContext → Monotonicity
  | .all => .upwardEntailing
  | .moreThanOne => .upwardEntailing
  | .exactlyTwo => .nonMonotonic
  | .notAll => .downwardEntailing
  | .notMoreThanOne => .downwardEntailing

/--
Experiment 3 result by quantifier and task.
-/
structure Exp3Result where
  /-- Quantifier context -/
  quantifier : QuantifierContext
  /-- Verification task rate (percentage saying "true") -/
  verificationTrueRate : Nat
  /-- Inference task rate (percentage endorsing local SI) -/
  inferenceRate : Nat
  deriving Repr

/--
Experiment 3 results (n=26).

Verification shows ~0% local SIs in UE contexts,
while inference shows ~50%. The verification task is more neutral.
-/
def exp3Results : List Exp3Result :=
  [ { quantifier := .all,           verificationTrueRate := 100, inferenceRate := 46 }
  , { quantifier := .moreThanOne,   verificationTrueRate := 100, inferenceRate := 62 }
  , { quantifier := .exactlyTwo,    verificationTrueRate := 100, inferenceRate := 50 }  -- averaged
  , { quantifier := .notAll,        verificationTrueRate := 4,   inferenceRate := 58 }
  , { quantifier := .notMoreThanOne, verificationTrueRate := 4,  inferenceRate := 46 }
  ]

/--
Verification shows no local SIs in UE contexts.

100% "true" means 0% local SI (since local SI would make it false).
-/
theorem verification_no_local_SI_in_UE :
    exp3Results.filter (λ r => quantifierMonotonicity r.quantifier == .upwardEntailing)
      |>.all (λ r => r.verificationTrueRate == 100) := by
  native_decide

/--
Inference task shows ~50% even in UE contexts.

This is an artifact of the inference paradigm, not genuine local SIs.
-/
theorem inference_around_chance :
    let ueResults := exp3Results.filter (λ r => quantifierMonotonicity r.quantifier == .upwardEntailing)
    let rates := ueResults.map (λ r => r.inferenceRate)
    rates.all (λ r => r > 40) ∧ rates.all (λ r => r < 70) := by
  native_decide

/--
For "all" quantifier: verification = 100% true, inference = 46%.
The 46-point gap is the task effect (inference creates spurious "local SIs").
-/
def allVerificationRate : Nat := 100
def allInferenceRate : Nat := 46

/--
Massive task effect in UE contexts.

Verification: 0% local SIs. Inference: ~50%. This ~46-point gap
shows the inference task creates spurious "local SIs".
-/
theorem task_effect_in_UE : allInferenceRate - (100 - allVerificationRate) > 40 := by
  native_decide


/--
Experiment 4 tested whether people can detect the "ambiguity"
that conventionalism predicts for scalar expressions.

If "some" is ambiguous between "some possibly all" and "some but not all",
people should recognize this ambiguity when given a "could be either" option.
-/
structure AmbiguityResult where
  /-- Description of sentence type -/
  sentenceType : String
  /-- Rate of "could be either" responses -/
  ambiguousRate : Nat
  deriving Repr

/--
Control sentences that are genuinely ambiguous.
People recognized these as ambiguous 70% of the time.
-/
def genuineAmbiguityResults : List AmbiguityResult :=
  [ { sentenceType := "The circles and squares are connected with each other", ambiguousRate := 82 }
  , { sentenceType := "The green and orange figures are connected", ambiguousRate := 73 }
  , { sentenceType := "All the figures are orange and green", ambiguousRate := 59 }
  , { sentenceType := "There are green circles and squares", ambiguousRate := 77 }
  , { sentenceType := "The circles and squares have the same colour", ambiguousRate := 59 }
  ]

/--
Average recognition rate for genuine ambiguities: 70%.
-/
def genuineAmbiguityAverage : Nat := 70

/--
Target sentences with alleged SI-induced "ambiguity".
People only said "could be either" 6% of the time.
-/
def allegedSIAmbiguityRate : Nat := 6

/--
Total responses consistent with conventionalism: only 10%.
(6% "could be either" + ~4% "false" responses)
-/
def totalConventionalistConsistent : Nat := 10

/--
People do not detect alleged SI ambiguities.

Conventionalism predicts ambiguity; participants don't see it.
-/
theorem no_SI_ambiguity_detected :
    allegedSIAmbiguityRate < 10 ∧
    genuineAmbiguityAverage - allegedSIAmbiguityRate > 60 := by
  native_decide

/--
Minimal support for conventionalism.

Only 10% of responses consistent with local SI readings.
-/
theorem minimal_conventionalist_support :
    totalConventionalistConsistent ≤ 10 := by
  native_decide


/--
Think embedding shows elevated rate vs other embeddings.

At 57%, think is the only embedding that shows substantial SI rate.
Other embeddings (all: 27%, must: 3%, want: 32%) are all below 35%.
-/
theorem think_elevated :
    thinkRate > 55 ∧
    27 < thinkRate - 20 ∧  -- all
    3 < thinkRate - 20 ∧   -- must
    32 < thinkRate - 20    -- want
    := by
  native_decide

/--
The central empirical finding: task affects inference rate.
-/
structure TaskEffectDatum where
  /-- Inference rate in inference task -/
  inferenceTaskRate : Nat
  /-- Inference rate in verification task -/
  verificationTaskRate : Nat
  /-- Is the difference significant? -/
  significantDifference : Bool
  deriving Repr

/--
The main finding: nearly 2x difference between tasks.
-/
def mainFinding : TaskEffectDatum :=
  { inferenceTaskRate := 62
  , verificationTaskRate := 34
  , significantDifference := true
  }

/--
Inference task shows higher rate than verification task.
-/
theorem inference_higher_than_verification :
    mainFinding.inferenceTaskRate > mainFinding.verificationTaskRate := by
  native_decide

/--
Verification rate is below 50%.

In the more neutral task, scalar inferences arise less than half
the time, arguing against weak defaultism.
-/
theorem verification_below_fifty :
    mainFinding.verificationTaskRate < 50 := by
  native_decide

/--
Task effect is substantial.

The inference task nearly doubles the rate.
-/
theorem task_effect_substantial :
    mainFinding.inferenceTaskRate > mainFinding.verificationTaskRate + 20 := by
  native_decide


/--
Data point from the experimental literature on scalar inference.
-/
structure LiteratureDatum where
  /-- Citation -/
  citation : String
  /-- Scalar term tested -/
  scalarTerm : String
  /-- Rate of upper-bounded interpretation (percentage) -/
  upperBoundRate : Nat
  deriving Repr

/--
Sample of experimental data from Geurts (2010) Table 1.
-/
def literatureData : List LiteratureDatum :=
  [ { citation := "Paris (1973)", scalarTerm := "or", upperBoundRate := 25 }
  , { citation := "Chevallier et al. (2008)", scalarTerm := "or", upperBoundRate := 25 }
  , { citation := "Pijnacker et al. (2009)", scalarTerm := "or", upperBoundRate := 54 }
  , { citation := "Paris (1973)", scalarTerm := "either/or", upperBoundRate := 32 }
  , { citation := "Evans & Newstead (1980)", scalarTerm := "either/or", upperBoundRate := 33 }
  , { citation := "Braine & Rumain (1981)", scalarTerm := "either/or", upperBoundRate := 41 }
  , { citation := "Noveck (2001)", scalarTerm := "some", upperBoundRate := 59 }
  , { citation := "Bott & Noveck (2004)", scalarTerm := "some", upperBoundRate := 59 }
  , { citation := "Feeney et al. (2004)", scalarTerm := "some", upperBoundRate := 65 }
  , { citation := "Geurts & Pouscoulous (2009)", scalarTerm := "some", upperBoundRate := 34 }
  , { citation := "Noveck (2001)", scalarTerm := "might", upperBoundRate := 65 }
  ]

/--
Average rate is below 50%.

Across the literature, scalar inference rates average below 50%.
-/
theorem average_below_fifty :
    (literatureData.map (·.upperBoundRate)).sum / literatureData.length < 50 := by
  native_decide

/--
No study exceeds 65%.

Even the highest rates are well below defaultism's predictions.
-/
theorem max_rate_below_seventy :
    literatureData.all (·.upperBoundRate < 70) := by
  native_decide

end Phenomena.ScalarImplicatures.Studies.GeurtsPouscoulous2009
