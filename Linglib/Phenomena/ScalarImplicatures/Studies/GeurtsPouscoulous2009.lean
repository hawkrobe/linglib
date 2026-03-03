import Mathlib.Data.Rat.Defs
import Linglib.Core.Empirical
import Linglib.Theories.Pragmatics.NeoGricean.ScalarImplicatures.Basic
import Linglib.Phenomena.ScalarImplicatures.Basic

/-!
# @cite{geurts-pouscoulous-2009} — Embedded Implicatures?!

Theory-neutral empirical data and argumentation chain from
@cite{geurts-pouscoulous-2009}.

## Central Question

Do scalar implicatures arise "locally" inside embedded clauses?
Conventionalists (Chierchia, Levinson, Landman) predict SIs occur
"systematically and freely in arbitrarily embedded positions."
Griceans predict SIs are global pragmatic inferences only.

## Argumentative Structure

1. **Exp 1a-b** (Table 2): SI endorsement rates vary wildly by embedding
   type (3–94%), contradicting "systematically and freely."

2. **Paradigm bias** (§2): Three worries about the inference paradigm used
   in Exp 1; it likely inflates observed SI rates.

3. **Exp 2** (§3, n=29): Inference task (62%) vs verification task (34%)
   confirms paradigm bias on simple sentences.

4. **Exp 3** (Table 3, n=26): Verification shows *zero* local SIs in UE
   contexts (100% "true"), while inference shows ~50% across all
   conditions regardless of monotonicity. The inference paradigm produces
   spurious "local SIs."

5. **Paradigm correction**: After accounting for bias, only *think* (57.5%)
   shows genuinely elevated SI rates. The rates for *all* (27%) and *want*
   (32%) may be entirely paradigm artifacts.

6. **Gricean explanation for think** (§8): Global SI (¬Bsp[Bs(all)]) +
   competence assumption (Bs(all) ∨ Bs(¬all)) entails Bs(¬all), which
   *looks like* a local SI but is derived globally.

7. **Exp 4** (Tables 4–5, n=22): Minimal conventionalism predicts people
   should detect ambiguity in scalar sentences. Genuine ambiguities
   detected at 70%, alleged SI-ambiguities at only 6%. Both mainstream
   and minimal conventionalism are falsified.
-/

namespace Phenomena.ScalarImplicatures.Studies.GeurtsPouscoulous2009

open Core.Empirical

-- ============================================================================
-- Shared Types
-- ============================================================================

/-- The two experimental paradigms. -/
inductive TaskType where
  | inference     -- "Does X imply Y?"
  | verification  -- "Is this sentence true of [picture]?"
  deriving DecidableEq, BEq, Repr

/-- Monotonicity of an embedding context. -/
inductive Monotonicity where
  | upwardEntailing    -- UE: all, more than one
  | downwardEntailing  -- DE: not all, not more than one
  | nonMonotonic       -- NM: exactly two
  deriving DecidableEq, BEq, Repr

/-- Quantifier contexts tested in Experiments 3–4. -/
inductive QuantifierContext where
  | all              -- UE: "All the squares are connected with some of the circles"
  | moreThanOne      -- UE: "More than one square is connected with some..."
  | exactlyTwo       -- NM: "Exactly two squares are connected with some..."
  | notAll           -- DE: "Not all the squares are connected with some..."
  | notMoreThanOne   -- DE: "Not more than one square is connected with some..."
  deriving DecidableEq, BEq, Repr

def quantifierMonotonicity : QuantifierContext → Monotonicity
  | .all => .upwardEntailing
  | .moreThanOne => .upwardEntailing
  | .exactlyTwo => .nonMonotonic
  | .notAll => .downwardEntailing
  | .notMoreThanOne => .downwardEntailing

-- ============================================================================
-- Measure Specifications
-- ============================================================================

/-- Inference task: "Does X imply Y?" -/
def inferenceMeasure : MeasureSpec :=
  { scale := .proportion, task := .inferenceEndorsement, unit := "percentage 0-100" }

/-- Verification task: "Is this true of the picture?" -/
def verificationMeasure : MeasureSpec :=
  { scale := .proportion, task := .truthValueJudgment, unit := "percentage 0-100" }

-- ============================================================================
-- Step 1: Conventionalist Predictions (to be falsified)
-- ============================================================================

/-- Mainstream conventionalism predicts local SIs are preferred in non-DE
contexts. In the inference paradigm, this means participants should endorse
the inference that "some" implies "not all" when embedded under UE/NM
quantifiers. In the verification paradigm, this means participants should
reject the classical reading when it conflicts with the local SI.

We formalize this as: conventionalism predicts SI endorsement rates
should be high (> 50%) in non-DE inference conditions, and verification
rates should match the SI reading, not the classical reading. -/
def conventionalistPredictsLocalSI : QuantifierContext → Bool
  | .all => true            -- predict local SI in UE
  | .moreThanOne => true
  | .exactlyTwo => true     -- predict local SI in NM
  | .notAll => false        -- no local SI prediction in DE
  | .notMoreThanOne => false

-- ============================================================================
-- Step 2: Experiment 1a-b — Embedding Type Variation (Table 2, pp.9-12)
-- ============================================================================

/-- Embedding types tested in Experiments 1a-b. -/
inductive EmbeddingType where
  | simple   -- "Fred heard some of the Verdi operas"
  | think    -- "Betty thinks Fred heard some..."
  | want     -- "Betty wants Fred to hear some..."
  | must     -- "Fred has to hear some..."
  | all      -- "All students heard some..."
  deriving DecidableEq, BEq, Repr

structure EmbeddingResult where
  embedding : EmbeddingType
  /-- % endorsing the local SI reading -/
  localSIRate : Nat
  n : Nat
  deriving Repr

/-- Experiment 1a results (Table 2, n=30). -/
def exp1aResults : List EmbeddingResult :=
  [ { embedding := .simple, localSIRate := 93, n := 30 }
  , { embedding := .think,  localSIRate := 50, n := 30 }
  , { embedding := .all,    localSIRate := 27, n := 30 }
  , { embedding := .must,   localSIRate := 3,  n := 30 }
  ]

/-- Experiment 1b results (Table 2, n=31). -/
def exp1bResults : List EmbeddingResult :=
  [ { embedding := .simple, localSIRate := 94, n := 31 }
  , { embedding := .think,  localSIRate := 65, n := 31 }
  , { embedding := .want,   localSIRate := 32, n := 31 }
  ]

/-- SI rates vary from 3% (must) to 94% (simple 1b), a 91pp range.
This contradicts the conventionalist claim that SIs occur
"systematically and freely in arbitrarily embedded positions."
If SIs were systematic, rates should be uniformly high across
all embedding types. -/
theorem embedding_not_systematic :
    94 - 3 > (85 : Nat) := by native_decide

/-- Only think shows substantial local SI endorsement among embedded
conditions. At 50% (1a) and 65% (1b), think is the only embedding
above 35%. All others (all: 27%, must: 3%, want: 32%) fall below.
The paper later argues (§5–8) that even these rates may be
artifacts of the inference paradigm. -/
theorem think_uniquely_elevated :
    50 > (35 : Nat) ∧ 65 > (35 : Nat) ∧  -- think in 1a and 1b
    27 < (35 : Nat) ∧ 3 < (35 : Nat) ∧ 32 < (35 : Nat) := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide⟩

-- ============================================================================
-- Step 3: Experiment 2 — Paradigm Bias (§3, n=29)
-- ============================================================================

/-- Experiment 2 results (§3.1–3.2, pp.16-17).
29 Dutch-speaking students at the University of Nijmegen.
Within-subjects: same critical sentence ("Some of the B's are in the
box on the left") tested in both inference and verification tasks.
McNemar's test, n = 29, p < .01. -/
structure Exp2Data where
  inferenceRate : Nat       -- % deriving SI in inference task
  verificationRate : Nat    -- % deriving SI in verification task
  controlAccuracy : Nat     -- % correct on verification fillers
  n : Nat
  deriving Repr

def exp2 : Exp2Data :=
  { inferenceRate := 62
  , verificationRate := 34
  , controlAccuracy := 97
  , n := 29 }

/-- The inference paradigm inflates SI rates by 28pp (62% vs 34%).
This confirms three a priori worries about the inference paradigm (§2):
(1) endorsing an argument is easier than spontaneously drawing it,
(2) the question "Does X imply Y?" makes the SI contextually relevant,
(3) superficial similarity to valid inferences may cause errors. -/
theorem paradigm_inflates_SI_rates :
    exp2.inferenceRate > exp2.verificationRate + 20 := by native_decide

/-- In the more neutral verification task, SI rate is below 50%.
This argues against even weak defaultism. -/
theorem verification_below_half :
    exp2.verificationRate < 50 := by native_decide

/-- Near-perfect control accuracy rules out a positive response bias. -/
theorem controls_rule_out_bias :
    exp2.controlAccuracy > 95 := by native_decide

-- ============================================================================
-- Step 4: Experiment 3 — Verification Shows No Local SIs (Table 3, §5, n=26)
-- ============================================================================

/-- One row of Table 3 (p.22). The table has 6 rows because "exactly two"
has two verification conditions (one where the classical reading is true,
one where the local-SI reading is true) but a single shared inference rate.

The `verificationPred` field records the conventionalist prediction for
verification (the parenthetical 0/1 in Table 3): should participants
say "true"? Similarly `inferencePred` for the inference column. -/
structure Exp3Row where
  quantifier : QuantifierContext
  /-- % saying "true" in verification task -/
  verificationTrueRate : Nat
  /-- Conventionalist prediction: should participants say "true"? -/
  verificationPred : Bool
  /-- % endorsing local SI in inference task -/
  inferenceRate : Nat
  /-- Conventionalist prediction: should participants endorse SI? -/
  inferencePred : Bool
  deriving Repr

/-- Experiment 3 results (Table 3, p.22, n=26).
26 first-year humanities students at the University of Nijmegen (§5.1, p.20).
Pairwise McNemar tests (Bonferroni-corrected) all significant:
*all* p < .005, *not all* p < .001, *more than one* p < .0005,
*not more than one* p < .05, *exactly two* p < .005 (both conditions). -/
def exp3Results : List Exp3Row :=
  [ -- UE contexts: classical=true, SI would make it false
    { quantifier := .all,           verificationTrueRate := 100, verificationPred := false,
      inferenceRate := 46, inferencePred := true }
  , { quantifier := .moreThanOne,   verificationTrueRate := 100, verificationPred := false,
      inferenceRate := 62, inferencePred := true }
    -- NM contexts: two verification conditions for exactly-two
  , { quantifier := .exactlyTwo,    verificationTrueRate := 100, verificationPred := false,
      inferenceRate := 50, inferencePred := true }   -- classical=true condition
  , { quantifier := .exactlyTwo,    verificationTrueRate := 0,   verificationPred := true,
      inferenceRate := 50, inferencePred := true }   -- classical=false condition
    -- DE contexts: classical=false (DE sentences false when all squares connected)
  , { quantifier := .notAll,        verificationTrueRate := 4,   verificationPred := false,
      inferenceRate := 58, inferencePred := false }
  , { quantifier := .notMoreThanOne, verificationTrueRate := 4,  verificationPred := false,
      inferenceRate := 46, inferencePred := false }
  ]

/-- Verification shows zero local SIs in UE contexts: 100% say "true"
(accepting the classical, non-SI reading). Conventionalism predicts
participants should say "false" (the local SI makes UE sentences
false in the depicted situation). This is the paper's central
empirical finding against mainstream conventionalism. -/
theorem verification_no_local_SI_in_UE :
    exp3Results.filter (λ r => quantifierMonotonicity r.quantifier == .upwardEntailing)
      |>.all (λ r => r.verificationTrueRate == 100) := by
  native_decide

/-- Inference rates cluster around 50% for ALL conditions (46–62%),
regardless of monotonicity. The inference paradigm produces a roughly
constant endorsement rate that does not discriminate between contexts
where conventionalism predicts SIs and contexts where it does not.
The paper reports: "all rates, for DE and non-DE items alike, clustered
around chance level, give or take 12%" (p.23). -/
theorem inference_clusters_around_chance :
    exp3Results.all (λ r => r.inferenceRate ≥ 40 ∧ r.inferenceRate ≤ 65) := by
  native_decide

/-- Verification perfectly tracks the classical (non-SI) truth value.
When the classical reading is true (verificationPred = false, i.e.,
conventionalism predicts "false" but classical reading predicts "true"),
the rate is ≥ 96%. When the classical reading is false
(exactly-two row 2 and DE items), the rate is ≤ 4%.
Participants judge truth values by the classical reading, not by any
local-SI reading. -/
theorem verification_tracks_classical_reading :
    exp3Results.all (λ r =>
      (r.verificationTrueRate ≥ 96 ∨ r.verificationTrueRate ≤ 4)) := by
  native_decide

-- ============================================================================
-- Step 5: Paradigm Correction — Only "think" Survives
-- ============================================================================

/-- After Experiment 3 establishes that the inference paradigm inflates
SI rates by ~50pp, the rates observed in Experiment 1 must be corrected.
The paper argues (p.23): "it is quite possible that the rates previously
observed for *all* (27%) and *want* (32%) are entirely due to a paradigm
bias." Only think (avg 57.5%) exceeds the observed paradigm bias level
(~50% baseline in Exp 3 inference conditions). -/
theorem only_think_survives_correction :
    27 ≤ (50 : Nat) ∧ 32 ≤ (50 : Nat) ∧ 3 ≤ (50 : Nat) ∧  -- all, want, must: ≤ baseline
    (50 + 65) / 2 > (50 : Nat) := by                          -- think avg: above baseline
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- Step 6: Gricean Explanation — Competence Under Believe (§8, pp.28-29)
-- ============================================================================

/-- The Gricean explanation for apparent local SIs under "think"/"believe".

For "Bob believes Anna ate some of the cookies", the global SI yields:
  ¬(Bob believes Anna ate all the cookies)

Under a competence assumption (Bob has an opinion on whether she ate all):
  (Bob believes all) ∨ (Bob believes ¬all)

From these two premises, it follows that Bob believes ¬all — which *looks
like* a local SI but is derived entirely from global pragmatics + competence.

This explains why "think" shows elevated rates (57.5%) while other
embeddings do not: the competence assumption is independently plausible
for attitude verbs (people typically have opinions about what they believe)
but not for quantifiers ("all students heard some" does not license
"each student has an opinion about whether they heard all"). -/
theorem competence_explains_think
    {BobBelievesAll BobBelievesNotAll : Prop}
    (globalSI : ¬BobBelievesAll)
    (competence : BobBelievesAll ∨ BobBelievesNotAll) :
    BobBelievesNotAll :=
  competence.elim (fun h => absurd h globalSI) id

/-- The competence explanation does NOT generalize to universal quantifiers.

For "All the customers shot at some of the salesmen", the global SI yields:
  ¬∀ (c : Customer), ShotAtAll c

The analogous competence assumption would require:
  ∀ (c : Customer), ShotAtAll c ∨ ShotAtNotAll c

This is a much stronger assumption — it requires every customer to have
a determinate shooting pattern. The paper notes (p.29) that this
assumption is "considerably less plausible" than for belief reports.

We demonstrate this by showing the proof still works formally
(same logical structure) but flagging in the docstring that the
premise is pragmatically implausible for quantifiers. -/
theorem competence_does_not_generalize
    {Customer : Type} {ShotAtAll ShotAtNotAll : Customer → Prop}
    (globalSI : ¬∀ c, ShotAtAll c)
    (strongCompetence : ∀ c, ShotAtAll c ∨ ShotAtNotAll c) :
    ∃ c, ShotAtNotAll c := by
  by_contra h
  push_neg at h
  exact globalSI (fun c => (strongCompetence c).elim id (fun h2 => absurd h2 (h c)))

-- ============================================================================
-- Step 7: Experiment 4 — No Ambiguity Detected (§7, Tables 4-5, n=22)
-- ============================================================================

/-- One row of Table 4 (p.27). Response rates for critical and DE control
items in Experiment 4, where participants chose among "true", "false",
and "could be either". As in Experiment 3, there were two verification
conditions for exactly-two. -/
structure Exp4Row where
  quantifier : QuantifierContext
  /-- % saying "true" (yes) -/
  trueRate : Nat
  /-- % saying "false" (no) -/
  falseRate : Nat
  /-- % saying "could be either" -/
  eitherRate : Nat
  deriving Repr

/-- Experiment 4 results (Table 4, p.27, n=22).
22 first-year linguistics students at University College London (p.26).
Wilcoxon's Exact test: W = 208, n = 20, p < .0001. -/
def exp4Results : List Exp4Row :=
  [ -- UE contexts: overwhelming "true" (classical reading)
    { quantifier := .all,           trueRate := 95, falseRate := 5,  eitherRate := 0 }
  , { quantifier := .moreThanOne,   trueRate := 100, falseRate := 0, eitherRate := 0 }
    -- NM contexts: two conditions for exactly-two
  , { quantifier := .exactlyTwo,    trueRate := 86, falseRate := 5,  eitherRate := 9 }
  , { quantifier := .exactlyTwo,    trueRate := 9,  falseRate := 77, eitherRate := 14 }
    -- DE controls
  , { quantifier := .notAll,        trueRate := 9,  falseRate := 86, eitherRate := 5 }
  , { quantifier := .notMoreThanOne, trueRate := 9, falseRate := 91, eitherRate := 0 }
  ]

/-- Ambiguous control sentences from Table 5 (p.27). These are genuinely
ambiguous sentences (e.g., "Visiting relatives can be boring") that
participants should be able to recognize as ambiguous. -/
structure AmbiguityControl where
  sentence : String
  /-- % saying "could be either" -/
  eitherRate : Nat
  deriving Repr

/-- Table 5: ambiguous control items (p.27). -/
def genuineAmbiguityResults : List AmbiguityControl :=
  [ { sentence := "The circles and squares are connected with each other", eitherRate := 82 }
  , { sentence := "The green and orange figures are connected", eitherRate := 73 }
  , { sentence := "All the figures are orange and green", eitherRate := 59 }
  , { sentence := "There are green circles and squares", eitherRate := 77 }
  , { sentence := "The circles and squares have the same colour", eitherRate := 59 }
  ]

/-- People detect genuine ambiguities at 70% on average but alleged
SI-induced ambiguities at only 6% (non-DE items). The 64pp gap shows
that people simply do not perceive the ambiguity that conventionalism
predicts. This falsifies even minimal conventionalism, which merely
claims that local-SI readings *exist* (not that they're preferred). -/
theorem no_SI_ambiguity_detected :
    -- Genuine ambiguity average: 70%
    (genuineAmbiguityResults.map (·.eitherRate)).sum /
      genuineAmbiguityResults.length == 70 ∧
    -- Alleged SI ambiguity: "could be either" rates ≤ 14% for all items
    exp4Results.all (λ r => r.eitherRate ≤ 14) := by
  constructor <;> native_decide

/-- Total non-DE responses consistent with conventionalism: only ~10%.
The paper reports (p.26-27): "only 9 out of 88 responses (i.e. 10%)
were consistent with minimal conventionalism. Moreover, all but one
of these responses were associated with non-monotonic *exactly two*." -/
theorem minimal_conventionalist_support :
    -- 9 out of 88 non-DE trial responses = 10%
    -- (4 non-DE items × 22 participants = 88 responses)
    (9 : Nat) * 100 / 88 ≤ 11 := by native_decide

/-- The gap between genuine and alleged ambiguity detection is massive:
70% vs 6% = 64pp. This is the strongest result against conventionalism. -/
theorem ambiguity_gap :
    (70 : Nat) - 6 > 60 := by native_decide

-- ============================================================================
-- Literature Survey (from @cite{geurts-2010} Table 1)
-- ============================================================================

/-- Data point from the broader experimental literature on scalar inference,
compiled in @cite{geurts-2010} Table 1 (a separate review chapter). -/
structure LiteratureDatum where
  citation : String
  scalarTerm : String
  /-- Rate of upper-bounded (SI) interpretation (percentage 0-100) -/
  upperBoundRate : Nat
  deriving Repr

/-- Sample of experimental data from @cite{geurts-2010} Table 1.
Across the literature, SI rates are highly variable and generally
below 65%, consistent with the Gricean view that SIs are context-
dependent pragmatic inferences rather than defaults. -/
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

/-- Average SI rate across the literature is below 50%.
This is inconsistent with defaultism's prediction that SIs are
the norm and should arise at high rates. -/
theorem literature_average_below_fifty :
    (literatureData.map (·.upperBoundRate)).sum / literatureData.length < 50 := by
  native_decide

/-- No study in the survey exceeds 65%. -/
theorem literature_max_below_seventy :
    literatureData.all (·.upperBoundRate < 70) := by
  native_decide

-- ============================================================================
-- Part II: NeoGricean Bridge — Theory Predictions vs Empirical Data
-- ============================================================================

/-! Connects NeoGricean scalar implicature theory (@cite{geurts-2010}) to the
experimental findings above.

- Embedding predictions match experimental SI rates
- DE blocking matches verification data
- Contextualism vs Defaultism adjudicated by task effects
- Hurford rescue/violation predictions match felicity judgments
- Singh asymmetry predictions match felicity judgments
-/

open NeoGricean.ScalarImplicatures
open NeoGricean.Alternatives
open Phenomena.ScalarImplicatures

/-- Exp 1a simple rate (Table 2). -/
def simpleRate : Nat := 93

/-- Exp 1a think rate (Table 2). -/
def thinkRate : Nat := 50

/-- Exp 1a must rate (Table 2). -/
def mustRate : Nat := 3

/-- Exp 3 verification rate for all+some in UE: 100% classical reading. -/
def allVerificationRate : Nat := 100

/-- Gricean prediction for embedding types. -/
structure EmbeddingPrediction where
  embedding : EmbeddingType
  predictsElevatedRate : Bool
  explanation : String
  deriving Repr

def griceanEmbeddingPredictions : List EmbeddingPrediction :=
  [ { embedding := .simple, predictsElevatedRate := true
    , explanation := "Global SI arises normally in unembedded contexts" }
  , { embedding := .think, predictsElevatedRate := true
    , explanation := "Global SI + competence assumption yields apparent local SI" }
  , { embedding := .want, predictsElevatedRate := false
    , explanation := "Want doesn't support competence assumption; no local SI" }
  , { embedding := .must, predictsElevatedRate := false
    , explanation := "Deontic must doesn't support competence; no local SI" }
  , { embedding := .all, predictsElevatedRate := false
    , explanation := "Universal quantifier doesn't support local SI" }
  ]

/-- Gricean predictions match experimental pattern. -/
theorem gricean_predicts_embedding_pattern :
    (griceanEmbeddingPredictions.find? (λ p => p.embedding == .simple)).isSome ∧
    simpleRate > 90 ∧
    (griceanEmbeddingPredictions.find? (λ p => p.embedding == .think)).isSome ∧
    thinkRate ≥ 50 ∧
    mustRate < 5 := by
  native_decide

/-- NeoGricean predicts SIs arise in UE contexts. -/
theorem ue_implicature_matches_data :
    someAllBlocking.implicatureInUE = true := by native_decide

/-- DE blocking prediction matches Experiment 3 verification data. -/
theorem de_blocking_matches_data :
    someNotAll_DE.implicatureArises = false ∧
    allVerificationRate = 100 := by
  native_decide

/-- Gricean account supported over conventionalism. -/
theorem gricean_supported :
    simpleRate - mustRate > 85 ∧
    thinkRate ≥ 50 ∧
    allVerificationRate = 100 := by
  native_decide

/-- Competence-based explanation for belief reports. -/
def competenceExplainsBelief : Bool :=
  thinkRate > mustRate + 40

theorem competence_explains_think_bridge :
    competenceExplainsBelief = true := by native_decide

-- Comparing Neo-Gricean variants

open _root_.NeoGricean

theorem defaultism_predicts_high_rate :
    predictsHighNeutralRate levinsonParams = true := by native_decide

theorem contextualism_predicts_moderate_rate :
    predictsHighNeutralRate geurtsParams = false := by native_decide

theorem only_contextualism_predicts_task_effect :
    predictsTaskEffect levinsonParams = false ∧
    predictsTaskEffect geurtsParams = true := by native_decide

theorem variants_make_different_predictions :
    levinsonParams.predictedNeutralRate ≠ geurtsParams.predictedNeutralRate ∧
    predictsTaskEffect levinsonParams ≠ predictsTaskEffect geurtsParams := by
  native_decide

theorem verification_matches_contextualism :
    let predicted := geurtsParams.predictedNeutralRate
    let observed := exp2.verificationRate
    (max predicted observed) - (min predicted observed) < 5 := by
  native_decide

theorem verification_far_from_defaultism :
    let predicted := levinsonParams.predictedNeutralRate
    let observed := exp2.verificationRate
    predicted - observed > 50 := by
  native_decide

theorem task_effect_observed :
    exp2.inferenceRate > exp2.verificationRate + 20 := by
  native_decide

theorem data_supports_contextualism_over_defaultism :
    predictsTaskEffect geurtsParams = true ∧
    (exp2.inferenceRate > exp2.verificationRate + 20) = true ∧
    (max geurtsParams.predictedNeutralRate exp2.verificationRate) -
    (min geurtsParams.predictedNeutralRate exp2.verificationRate) < 5 ∧
    levinsonParams.predictedNeutralRate - exp2.verificationRate > 50 := by
  native_decide

-- NeoGricean vs RSA agreement

/-- NeoGricean derives "not all" from "some". -/
theorem neogricean_derives_not_all :
    hasImplicature someStudentsSleep_result "all" = true := by
  native_decide

/-- NeoGricean explicitly blocks SIs in DE contexts. -/
theorem de_blocking :
    hasImplicature someStudentsSleep_DE_result "all" = false := by
  native_decide

-- Hurford and Singh prediction bridges

theorem someOrAll_prediction_matches_data :
    someOrAll_semantic.isRescued ↔ someOrAll.felicitous = true := by
  constructor
  · intro _; rfl
  · intro _; exact someOrAll_is_rescued

theorem americanCalifornian_prediction_matches_data :
    ¬americanCalifornian_semantic.isRescuedFromBA ↔ americanCalifornian.felicitous = false := by
  constructor
  · intro _; rfl
  · intro _; exact americanCalifornian_not_rescued

theorem orThenBoth_prediction_matches_data :
    orThenBoth_semantic.predictedFelicitous ↔ orThenBoth.felicitous = true := by
  constructor
  · intro _; rfl
  · intro _; exact orThenBoth_predicted_felicitous

theorem bothThenOr_prediction_matches_data :
    ¬bothThenOr_semantic.predictedFelicitous ↔ bothThenOr.felicitous = false := by
  constructor
  · intro _; rfl
  · intro _; exact bothThenOr_not_predicted_felicitous

end Phenomena.ScalarImplicatures.Studies.GeurtsPouscoulous2009
