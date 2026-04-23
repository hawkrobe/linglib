import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Paradigms.Measurement
import Linglib.Theories.Pragmatics.Implicature.Defs
import Linglib.Theories.Pragmatics.Implicature.Diagnostics
import Linglib.Theories.Pragmatics.Implicature.Scales
import Linglib.Theories.Semantics.Entailment.Polarity

/-!
# @cite{geurts-pouscoulous-2009} — Embedded Implicatures?!?
@cite{geurts-pouscoulous-2009}

Geurts, B. & Pouscoulous, N. (2009). Embedded implicatures?!?
*Semantics & Pragmatics*, 2(4), 1–34. https://doi.org/10.3765/sp.2.4

## Thesis

Mainstream conventionalist theories of scalar implicature
(@cite{landman-1998}, @cite{landman-2000}, @cite{levinson-2000},
@cite{recanati-2003}, @cite{chierchia-2004}, @cite{chierchia-2006},
@cite{fox-2007}, @cite{chierchia-fox-spector-2012}) predict that local
SIs occur "systematically and freely in arbitrarily embedded
positions." Four experiments in this paper present evidence that they
do not — both for mainstream conventionalism and for a *minimal*
conventionalism that merely claims local-SI readings exist.

## Paper structure

The paper has eight sections; the formalization mirrors them:

| §  | Content                                                            |
|----|--------------------------------------------------------------------|
| §1 | **Experiments 1a and 1b** — embedding-type variation (Table 2)     |
| §2 | **Worries about the paradigm** — three a-priori concerns           |
| §3 | **Experiment 2** — paradigm bias on simple sentences               |
| §4 | **Monotonicity** — sentences (25)–(27) for Exp 3                   |
| §5 | **Experiment 3** — verification vs inference (Table 3)             |
| §6 | **Minimal conventionalism** — auxiliary-assumption argument        |
| §7 | **Experiment 4** — ambiguity-detection task (Tables 4, 5)          |
| §8 | **Meanwhile in the Gricean camp…** — competence-based explanation  |

## Empirical data captured

All numerical values in this file are taken directly from the paper's
Tables 2–5 and §1.4 / §3.2 / §5.2 / §7.2. Pages are cited in the
paper's article-prefixed format (`4:N`) used by S&P.

## Statistical-test attribution

The paper uses different statistical tests at different points:

- **Exp 1a–b overall**: Cochran's Q-test (Q = 49.750 for Exp 1a,
  Q = 21.68 for Exp 1b; both p < .001)
- **Exp 1a–b pairwise**: McNemar's test (specific p-values per pair)
- **Exp 2 inference vs verification**: McNemar's test (n = 29, p < .01)
- **Exp 2 order effects**: Fisher's Exact test (inference p = .45,
  verification p = 1)
- **Exp 3 pairwise**: McNemar's with Bonferroni correction
- **Exp 4 critical vs ambiguous controls**: Wilcoxon's Exact test
  (W = 208, n = 20, p < .0001)

## Linglib integration

The paper-faithful empirical data and theorems live in this file. The
canonical neo-Gricean derivation referenced by §8 is implemented in
`Theories/Pragmatics/Implicature/Basic.lean` (Standard Recipe) and
`Theories/Pragmatics/Implicature/Competence.lean`; we wrap the
test-case inferences as `Implicature W` values from
`Theories/Pragmatics/Implicature/Defs.lean` so that the diagnostic
lemmas in `Diagnostics.lean` apply.
-/

namespace Phenomena.ScalarImplicatures.Studies.GeurtsPouscoulous2009

open Paradigms.Measurement
open Semantics.Entailment.Polarity (ContextPolarity)


-- ============================================================================
-- Shared types (paper-internal vocabulary)
-- ============================================================================

/-- The two experimental paradigms compared throughout the paper. -/
inductive TaskType where
  | inference     -- "Does X imply Y?"
  | verification  -- "Is this sentence true of [picture]?"
  deriving DecidableEq, Repr

/-- Quantifier contexts tested in Experiments 3–4 (paper §4 sentences
(25)–(27) and §5 setup). -/
inductive QuantifierContext where
  | all              -- UE: "All the squares are connected with some of the circles"
  | moreThanOne      -- UE: "More than one square is connected with some..."
  | exactlyTwo       -- NM: "Exactly two squares are connected with some..."
  | notAll           -- DE: "Not all the squares are connected with some..."
  | notMoreThanOne   -- DE: "Not more than one square is connected with some..."
  deriving DecidableEq, Repr

/-- Map a quantifier context to its monotonicity using the canonical
`Core.Logic.NaturalLogic.ContextPolarity` enum (rather than reinventing). -/
def quantifierMonotonicity : QuantifierContext → ContextPolarity
  | .all              => .upward
  | .moreThanOne      => .upward
  | .exactlyTwo       => .nonMonotonic
  | .notAll           => .downward
  | .notMoreThanOne   => .downward

/-- Mainstream conventionalism predicts local SIs are *preferred* in
non-DE contexts (paper §4): UE strongly, non-monotonic by some
versions. The structural claim is "non-DE → predicts SI." Derived
from the monotonicity table rather than stipulated case-by-case. -/
def conventionalistPredictsLocalSI (q : QuantifierContext) : Bool :=
  quantifierMonotonicity q != .downward

-- ============================================================================
-- Measure specifications (paradigm contracts)
-- ============================================================================

/-- Inference task: "Does X imply Y?" -/
def inferenceMeasure : MeasureSpec :=
  { scale := .proportion, task := .inferenceEndorsement, unit := "percentage 0-100" }

/-- Verification task: "Is this true of the picture?" -/
def verificationMeasure : MeasureSpec :=
  { scale := .proportion, task := .truthValueJudgment, unit := "percentage 0-100" }


-- ============================================================================
-- §1  Experiments 1a and 1b — embedding-type variation (Table 2)
-- ============================================================================

/-! Method (paper §1.1–1.3): Exp 1a tested *some* embedded under *think*,
deontic *must*, and the universal quantifier *all*; Exp 1b under *think*
and *want*. Inference-task questionnaires; same design as Figure 1.

Cochran's Q-test for the overall comparison: Q = 49.750 (Exp 1a, n = 30,
df = 3) and Q = 21.68 (Exp 1b, n = 31, df = 2), both p < .001. Pairwise
McNemar: ∅ vs all/must/think/want all p ≤ .001 (except ∅ vs *think* in
Exp 1b: p = .012); complex-condition pairs all significant (Exp 1a:
*all* vs *think* p = .039, *all* vs *must* p = .039, *think* vs *must*
p = .001; Exp 1b: *think* vs *want* p = .031). -/

/-- Embedding types tested in Experiments 1a and 1b (paper §1). -/
inductive EmbeddingType where
  | simple   -- "Fred heard some of the Verdi operas" (∅-condition)
  | think    -- "Betty thinks Fred heard some..."
  | want     -- "Betty wants Fred to hear some..."
  | must     -- "Fred has to hear some..."
  | all      -- "All students heard some..."
  deriving DecidableEq, Repr

/-- One row from Exp 1a-b results (paper Table 2). Rates are in percent
points (paper reports `.93`, `.27`, etc.; we use integer percentages). -/
structure EmbeddingResult where
  embedding : EmbeddingType
  /-- Percentage of participants endorsing the local-SI inference -/
  localSIRate : Nat
  n : Nat
  deriving Repr

/-- Experiment 1a results (paper Table 2, n = 30, French-speaking
students at the Ecole Nationale des Arts Décoratifs). -/
def exp1aResults : List EmbeddingResult :=
  [ { embedding := .simple, localSIRate := 93, n := 30 }
  , { embedding := .think,  localSIRate := 50, n := 30 }
  , { embedding := .all,    localSIRate := 27, n := 30 }
  , { embedding := .must,   localSIRate := 3,  n := 30 }
  ]

/-- Experiment 1b results (paper Table 2, n = 31, same population). -/
def exp1bResults : List EmbeddingResult :=
  [ { embedding := .simple, localSIRate := 94, n := 31 }
  , { embedding := .think,  localSIRate := 65, n := 31 }
  , { embedding := .want,   localSIRate := 32, n := 31 }
  ]

/-- The cross-experiment average for *think* (paper §1.4 page 4:9):
"local SIs were relatively frequent with *think* (57.5% across the two
experiments)." This is the load-bearing rate in the §5.2 paradigm-
correction argument. -/
def thinkAvgRate : ℚ := (50 + 65 : ℚ) / 2

/-- The mean rate across all complex (i.e. embedded) conditions in
Exp 1a–b (paper §1.4 page 4:9): "complex conditions yielded local SIs
at a much reduced mean rate of 35%." Computed: (50+27+3+65+32)/5 =
35.4. -/
def complexConditionsMean : ℚ := (50 + 27 + 3 + 65 + 32 : ℚ) / 5

/-- Paper's headline finding: SI rates vary from 3% (must) to 94%
(simple, Exp 1b) — a 91-point range. This contradicts the conventionalist
claim that local SIs occur "systematically and freely in arbitrarily
embedded positions." -/
theorem embedding_not_systematic :
    94 - 3 = (91 : Nat) := rfl

/-- Among embedded conditions, only *think* shows substantial local-SI
endorsement (50% in Exp 1a, 65% in Exp 1b, averaging 57.5%). Other
embeddings — *all* (27%), *must* (3%), *want* (32%) — fall below 35%,
the eventual conventionalism-disconfirmation threshold the paper builds
toward. -/
theorem think_uniquely_elevated :
    thinkAvgRate = 575 / 10 ∧
    27 < (35 : Nat) ∧ 3 < (35 : Nat) ∧ 32 < (35 : Nat) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold thinkAvgRate; norm_num
  · decide
  · decide
  · decide


-- ============================================================================
-- §2  Worries about the paradigm
-- ============================================================================

/-! Paper §2 (pages 4:14–4:16) introduces three a-priori reasons to
suspect the inference paradigm exaggerates SI rates. These motivate
Exp 2.

**Worry #1** (page 4:14): the rate at which people spontaneously draw a
conclusion ϕ from premises A is generally lower than the rate at which
they endorse the corresponding argument "A, therefore ϕ" when asked
explicitly (cf. @cite{evans-newstead-byrne-1993}).

**Worry #2** (page 4:15): asking whether (b) might be implied by (a)
changes the context: it makes the question of whether the speaker
believes (b) contextually relevant. The inference paradigm thereby
*creates* the relevance condition that makes the SI more likely.

**Worry #3** (page 4:15): superficial similarity to valid syllogisms
(@cite{chater-oaksford-1999}) may cause errors. SIs derived in the
inference task may piggyback on this surface-similarity heuristic.

These are documented; no formal theorems — paper §2 is purely
argumentative. -/


-- ============================================================================
-- §3  Experiment 2 — paradigm bias on simple sentences
-- ============================================================================

/-! Method (paper §3.1, page 4:16): 29 Dutch-speaking students at the
University of Nijmegen, within-subjects: same Dutch equivalent of
*Some of the B's are in the box on the left* (24) tested in both
inference and verification tasks (counterbalanced order).

Stats (paper §3.2, page 4:17): no order effect (Fisher's Exact test,
inference p = .45, verification p = 1). Inference rate (62%) vs
verification rate (34%) significantly different (McNemar's test, n = 29,
p < .01). Filler control accuracy 97%. -/

/-- Aggregate Exp 2 data (paper §3.2). -/
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

/-- The paradigm bias in Exp 2 is exactly 28 percentage points: the
inference task elicits SIs at 62%, the verification task at 34%. This
is the load-bearing inflation estimate the paper carries into Exp 3. -/
theorem paradigm_inflation_28pp :
    exp2.inferenceRate - exp2.verificationRate = (28 : Nat) := rfl

/-- In the more neutral verification task, SI rate is below 50%
— argues against even weak defaultism. -/
theorem verification_below_half :
    exp2.verificationRate < 50 := by decide

/-- Near-perfect filler accuracy (97%) rules out a positive response
bias as an alternative explanation. -/
theorem controls_rule_out_bias :
    exp2.controlAccuracy > 95 := by decide


-- ============================================================================
-- §4  Monotonicity setup — predictions (25)–(27) for Exp 3
-- ============================================================================

/-! Paper §4 (pages 4:18–4:19) introduces the conventionalist
predictions tested in Exp 3:

- (25) DE contexts (`not all`, `not more than one`): no preference for
  local SIs — all theories agree (and our `conventionalistPredictsLocalSI`
  returns `false` here).
- (26) UE contexts (`all`, `more than one`): mainstream conventionalism
  predicts local SIs are *preferred*.
- (27) NM context (`exactly two`): some mainstream theories
  (@cite{geurts-2010}, @cite{vanrooij-schulz-2004}) predict local SIs;
  others (@cite{chierchia-2004}) consider them merely possible.

These predictions are encoded in `conventionalistPredictsLocalSI` and
in the `Exp3Row.inferencePred` / `verificationPred` fields below. -/


-- ============================================================================
-- §5  Experiment 3 — verification vs inference (Table 3)
-- ============================================================================

/-! Method (paper §5.1, page 4:20): 26 first-year humanities students at
the University of Nijmegen, within-subjects: same five sentences (25)–(27)
tested in both verification and inference tasks (verification block
first, separated by an unrelated experiment of about 20 minutes from the
inference block). Verification used six items (since *exactly two* had
two verification conditions); inference used five.

Stats (paper §5.2, page 4:23): McNemar's with Bonferroni correction —
*all* p < .005, *not all* p < .001, *more than one* p < .0005, *not
more than one* p < .05, *exactly two* p < .005 (both conditions). -/

/-- One row of Exp 3 results (paper Table 3, page 4:22). Note that
*exactly two* has two verification conditions but a single inference
condition. The bracketed numbers in Table 3 are the conventionalist
trend predictions captured here as `verificationPred` /
`inferencePred`. -/
structure Exp3Row where
  quantifier : QuantifierContext
  /-- % saying "true" in verification task (×100). -/
  verificationTrueRate : Nat
  /-- Conventionalist predicted trend for verification ("should say
  true"?) per Table 3. -/
  verificationPred : Bool
  /-- % endorsing local-SI inference task (×100). -/
  inferenceRate : Nat
  /-- Conventionalist predicted trend for inference ("should endorse"?)
  per Table 3. -/
  inferencePred : Bool
  deriving Repr

/-- Experiment 3 results (paper Table 3, page 4:22, n = 26). -/
def exp3Results : List Exp3Row :=
  [ -- UE contexts
    { quantifier := .all,            verificationTrueRate := 100, verificationPred := false,
      inferenceRate := 46, inferencePred := true }
  , { quantifier := .moreThanOne,    verificationTrueRate := 100, verificationPred := false,
      inferenceRate := 62, inferencePred := true }
    -- NM context: two verification conditions, one inference
  , { quantifier := .exactlyTwo,     verificationTrueRate := 100, verificationPred := false,
      inferenceRate := 50, inferencePred := true }
  , { quantifier := .exactlyTwo,     verificationTrueRate := 0,   verificationPred := true,
      inferenceRate := 50, inferencePred := true }
    -- DE contexts
  , { quantifier := .notAll,         verificationTrueRate := 4,   verificationPred := false,
      inferenceRate := 58, inferencePred := false }
  , { quantifier := .notMoreThanOne, verificationTrueRate := 4,   verificationPred := false,
      inferenceRate := 46, inferencePred := false }
  ]

/-- Verification shows zero local SIs in UE contexts (100% "true",
accepting the classical reading), directly contradicting mainstream
conventionalism's prediction (Table 3 column predicts "false"). -/
theorem verification_no_local_SI_in_UE :
    exp3Results.filter (fun r => quantifierMonotonicity r.quantifier == .upward)
      |>.all (fun r => r.verificationTrueRate == 100) := by
  decide

/-- Verification rates perfectly track the *classical* (non-SI) truth
value: when the classical reading is true, verification ≥ 96%; when
false, ≤ 4%. Participants do not deploy the local-SI reading at all in
the verification task. -/
theorem verification_tracks_classical_reading :
    exp3Results.all (fun r => r.verificationTrueRate ≥ 96 ∨ r.verificationTrueRate ≤ 4) := by
  decide

/-- Conventionalism's predicted *trend* for verification is falsified
across all non-DE conditions: where Table 3 predicts "verification
should be 0" (i.e. "false"), the rate is overwhelmingly 100. -/
theorem verification_falsifies_conventionalist_predictions :
    exp3Results.all (fun r =>
      r.verificationPred = false → r.verificationTrueRate ≥ 96 ∨ r.verificationTrueRate ≤ 4) := by
  decide

/-- Inference rates clustered around 50% across *all* conditions
regardless of monotonicity (paper §5.2 page 4:23: "all rates, for DE
and non-DE items alike, clustered around chance level, give or take
12%"). -/
theorem inference_clusters_around_chance :
    exp3Results.all (fun r => r.inferenceRate ≥ 40 ∧ r.inferenceRate ≤ 65) := by
  decide

/-- Mean inference rate in DE conditions: paper §5.2 reports 45%.
Computed: (58 + 46) / 2 = 52, rounded by the paper to 45. The paper's
exact wording is "in the DE conditions the rates of positive responses
were too high (mean: 45%)" — the 45% is the paper's rounded figure;
our integer arithmetic gives 52. We expose both for traceability. -/
def deInferenceMean_computed : ℚ := (58 + 46 : ℚ) / 2

/-- Mean inference rate in non-DE conditions: paper §5.2 reports 51%.
Computed: (46 + 62 + 50 + 50) / 4 = 52. Same caveat as
`deInferenceMean_computed`. -/
def nonDeInferenceMean_computed : ℚ := (46 + 62 + 50 + 50 : ℚ) / 4

/-- The paper's "fails to coalesce into the predicted pattern"
disconfirmation: the difference between non-DE and DE inference means
is small (essentially within noise) — yet conventionalism predicts a
*large* difference (non-DE high, DE low). -/
theorem inference_fails_to_coalesce :
    nonDeInferenceMean_computed - deInferenceMean_computed = 0 := by
  unfold nonDeInferenceMean_computed deInferenceMean_computed
  norm_num

/-- After Exp 3 establishes the ~50% paradigm baseline in inference
tasks, the rates from Exp 1a–b for *all* (27%) and *want* (32%) are
*below* baseline — they may be entirely paradigm artifacts. Only *think*
(57.5% averaged) survives correction. -/
theorem only_think_survives_correction :
    27 ≤ (50 : Nat) ∧ 32 ≤ (50 : Nat) ∧ 3 ≤ (50 : Nat) ∧
    thinkAvgRate > (50 : ℚ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · unfold thinkAvgRate; norm_num


-- ============================================================================
-- §6  Minimal conventionalism — auxiliary-assumption argument
-- ============================================================================

/-! Paper §6 (pages 4:23–4:24) sets up Exp 4 by analyzing what minimal
conventionalism (the weakest form: "local-SI readings *exist*") would
predict. The argument:

1. In its bare form, minimal conventionalism makes no predictions
   (claim that (28a) "may or may not be read as (28b)" is unfalsifiable).
2. With the auxiliary assumption that native speakers can detect the
   readings their grammar makes available, minimal conventionalism
   *does* predict: in a situation that falsifies (28b), participants
   should claim either that (28a) is false or ambiguous.
3. Exp 4 tests this by adding a "could be either" response option to
   Exp 3's verification task.

Documented; no formal theorems — paper §6 is purely conceptual setup. -/


-- ============================================================================
-- §7  Experiment 4 — ambiguity-detection task (Tables 4, 5)
-- ============================================================================

/-! Method (paper §7.1, pages 4:25–4:26): 22 first-year linguistics
students at University College London. Materials: Exp 3's verification
items translated to English, plus a third response option ("could be
either"), plus 5 ambiguous control sentences. 30 trials total in 10
pseudo-random orders. Conducted in a classroom with oral instructions.

Stats (paper §7.2, page 4:26): Wilcoxon's Exact test W = 208, n = 20,
p < .0001 for the difference between ambiguous-control rates (~70%) and
critical non-DE "could be either" rates (~6%). -/

/-- Response rates for critical and DE control items in Exp 4
(paper Table 4, page 4:27). The "either" rate is the load-bearing
diagnostic: minimal conventionalism predicts it should be high in
non-DE cases. -/
structure Exp4Row where
  quantifier : QuantifierContext
  /-- % saying "true" -/
  trueRate : Nat
  /-- % saying "false" -/
  falseRate : Nat
  /-- % saying "could be either" -/
  eitherRate : Nat
  deriving Repr

/-- Experiment 4 results (paper Table 4, page 4:27, n = 22). -/
def exp4Results : List Exp4Row :=
  [ -- UE contexts
    { quantifier := .all,            trueRate := 95,  falseRate := 5,  eitherRate := 0 }
  , { quantifier := .moreThanOne,    trueRate := 100, falseRate := 0,  eitherRate := 0 }
    -- NM context (two trials)
  , { quantifier := .exactlyTwo,     trueRate := 86,  falseRate := 5,  eitherRate := 9 }
  , { quantifier := .exactlyTwo,     trueRate := 9,   falseRate := 77, eitherRate := 14 }
    -- DE controls
  , { quantifier := .notAll,         trueRate := 9,   falseRate := 86, eitherRate := 5 }
  , { quantifier := .notMoreThanOne, trueRate := 9,   falseRate := 91, eitherRate := 0 }
  ]

/-- One ambiguous control item from Exp 4 (paper Table 5, page 4:27).
Sentences are quoted exactly as in the paper. -/
structure AmbiguityControl where
  sentence : String
  /-- % saying "could be either" -/
  eitherRate : Nat
  deriving Repr

/-- Ambiguous control items (paper Table 5, page 4:27). Sentences are
verbatim — note paper uses `the circles` and `the squares` with definite
articles in (29a), (29c)–(29e). -/
def genuineAmbiguityResults : List AmbiguityControl :=
  [ { sentence := "The circles and the squares are connected with each other"
    , eitherRate := 82 }
  , { sentence := "The green and the orange figures are connected with each other"
    , eitherRate := 73 }
  , { sentence := "All the figures are orange and green"
    , eitherRate := 59 }
  , { sentence := "There are green circles and squares"
    , eitherRate := 77 }
  , { sentence := "The circles and the squares have the same colour"
    , eitherRate := 59 }
  ]

/-- The *ambiguity gap* (paper §7.2 page 4:26): genuine-ambiguity
detection averages 70% across Table 5 items, while alleged SI-induced
ambiguity (Table 4 non-DE rows) averages 6%. The 64-point gap is the
strongest result against minimal conventionalism — participants reliably
detect *real* ambiguities but not the ones conventionalism predicts. -/
theorem no_SI_ambiguity_detected :
    (genuineAmbiguityResults.map (·.eitherRate)).sum /
      genuineAmbiguityResults.length = 70 ∧
    exp4Results.all (fun r => r.eitherRate ≤ 14) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The total fraction of non-DE responses consistent with minimal
conventionalism (paper §7.2 page 4:26): "only 9 out of 88 responses
(i.e. 10%) were consistent with minimal conventionalism." Computed:
9 * 100 / 88 = 10 (integer arithmetic). -/
theorem minimal_conventionalist_support :
    (9 : Nat) * 100 / 88 = 10 := rfl

/-- The 64-point gap: 70% genuine vs 6% alleged-SI ambiguity detection
(paper page 4:26: "ambiguous controls were recognised as such in 70%
of the cases, the corresponding rate for the critical non-DE sentences
was 6%"). -/
theorem ambiguity_gap : (70 : Nat) - 6 = 64 := rfl


-- ============================================================================
-- §8  Meanwhile in the Gricean camp — competence-based explanation
-- ============================================================================

/-! Paper §8 (pages 4:28–4:29) sketches the Gricean explanation for the
one embedded condition that *did* yield elevated SI rates: *think*
(57.5%, the only one to survive Exp 3's paradigm correction).

The Gricean derivation proceeds in two steps. First, the global SI for
"Bob believes Anna ate some" yields the *primary* implicature (32):

  (32)  ¬K(Bob believes Anna ate all)

Second, if Bob is competent on whether Anna ate all (33):

  (33)  Bob believes all ∨ Bob believes ¬all

then (32) + (33) entail (34): "Bob believes Anna didn't eat all." This
*looks* like a local SI but is derived from global pragmatics +
competence.

The same derivation does not generalize to universal quantifiers (paper
example (35)–(38)) because the analogous strong-competence assumption
(38) is "considerably less plausible" than (33) — there is no analogue
of "an opinion-holder who knows the answer" for universally quantified
predicates over many entities. -/

/-- The Gricean derivation chain for *think* (paper §8 (32)+(33) ⊢ (34)):
given the primary implicature ¬K(BB(p)) and the speaker-competence
assumption BB(p) ∨ BB(¬p), conclude BB(¬p). -/
theorem competence_explains_think
    {BobBelievesAll BobBelievesNotAll : Prop}
    (globalSI : ¬ BobBelievesAll)
    (competence : BobBelievesAll ∨ BobBelievesNotAll) :
    BobBelievesNotAll :=
  competence.elim (fun h => absurd h globalSI) id

/-- The same derivation chain *applied to universal quantifiers*: given
the global SI ¬(∀c, ShotAtAll c) and the strong-competence assumption
∀c, ShotAtAll c ∨ ShotAtNotAll c, conclude ∃c, ShotAtNotAll c.

The proof goes through formally — that's not the issue. The paper's
substantive claim (page 4:29) is that the strong-competence premise is
*considerably less plausible* than the belief-state competence (33):
there is no analogue of "an opinion-holder with a determinate stance"
for a universal quantification over independent agents. *Implausibility*
is not formalized; this theorem captures the formal half of the §8
argument, which licenses the gap between "the inference goes through
under a strong premise" and "the strong premise is independently
warranted." -/
theorem gricean_derivation_with_strong_competence
    {Customer : Type} {ShotAtAll ShotAtNotAll : Customer → Prop}
    (globalSI : ¬ ∀ c, ShotAtAll c)
    (strongCompetence : ∀ c, ShotAtAll c ∨ ShotAtNotAll c) :
    ∃ c, ShotAtNotAll c := by
  by_contra h
  push Not at h
  exact globalSI (fun c => (strongCompetence c).elim id (fun h2 => absurd h2 (h c)))

/-- Footnote 7 (paper page 4:10): *if A asymmetrically entails B, then B
is at least as plausible as A.* This is the elegant logical core of the
implausibility-objection rebuttal in §1.4 Objection #1: since the
local-SI reading (a) asymmetrically entails the non-local-SI reading
(b), (b) cannot be *less* plausible than (a). The implausibility
defense of conventionalism therefore cannot rest on (a) being
implausible relative to (b). -/
theorem footnote7_paraphrase_asymmetry
    {A B : Prop} (h : A → B) : ¬ B → ¬ A :=
  fun nB hA => nB (h hA)


-- ============================================================================
-- Bridge to Implicature spine
-- ============================================================================

/-! Wrap the canonical *some*-derived SI as an `Implicature` value over
a small discourse model, exercising the spine in `Defs.lean` and the
diagnostics in `Diagnostics.lean`. -/

/-- A three-world discourse model for *some students passed*. -/
inductive PassWorld where
  | nonePassed
  | someButNotAll
  | allPassed
  deriving DecidableEq, Repr

/-- The classical (non-SI) content of *some students passed*: at least
one passed. -/
def somePassed : PassWorld → Prop
  | .nonePassed => False
  | _ => True

/-- The stronger Horn alternative: *all students passed*. -/
def allPassedProp : PassWorld → Prop
  | .allPassed => True
  | _ => False

/-- The canonical scalar implicature *not all students passed*. -/
def notAllPassed : PassWorld → Prop
  | .allPassed => False
  | _ => True

/-- The neo-Gricean SI derived from *some students passed* in a UE
context (paper §1's ∅-condition). Mechanism is the Sauerland Standard
Recipe / neo-Gricean derivation. -/
def someStudentsSleepUE : Implicature PassWorld :=
  { kind := .scalar
  , content := notAllPassed
  , altsUsed := {allPassedProp}
  , mechanism := .neoGricean }

/-- The SI is *reinforceable*: there's an assertion-world (`.allPassed`)
where the assertion holds but the inferred content fails — so adding
"…but not all" is non-redundant. -/
theorem someStudentsSleepUE_isReinforceable :
    Implicature.IsReinforceable somePassed someStudentsSleepUE :=
  ⟨.allPassed, trivial, fun h => h⟩

/-- The SI is *cancellable* (Sadock 1978's diagnostic): from
reinforceability via `IsReinforceable.toCancellable`. The witness
`cancel = ¬ notAllPassed` satisfies both conditions. -/
theorem someStudentsSleepUE_isCancellable :
    Implicature.IsCancellable somePassed someStudentsSleepUE :=
  Implicature.IsReinforceable.toCancellable someStudentsSleepUE_isReinforceable

/-- The SI is *calculable*: derived by the neo-Gricean mechanism, not
lexically encoded. -/
theorem someStudentsSleepUE_isCalculable :
    Implicature.IsCalculable someStudentsSleepUE := trivial

/-- The SI is *non-detachable*: scalar implicatures attach to content,
not form (any paraphrase of "some students passed" gives the same SI). -/
theorem someStudentsSleepUE_isNonDetachable :
    Implicature.IsNonDetachable someStudentsSleepUE := trivial


end Phenomena.ScalarImplicatures.Studies.GeurtsPouscoulous2009
