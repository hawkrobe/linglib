import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Theories.Pragmatics.RSA.Core.Distribution
import Linglib.Core.MeasurementScale
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# Lassiter & Goodman (2017) — Threshold RSA for Vague Adjectives

"Adjectival vagueness in a Bayesian model of interpretation"
Synthese 194:3801–3836

## Innovation

Standard RSA: `P_L1(w | u) ∝ P_S1(u | w) × P(w)`

Threshold RSA: `P_L1(w, θ | u) ∝ P_S1(u | w, θ) × P(w) × P(θ)`

The listener jointly infers:
- The world state (e.g., the height of the person being described)
- The threshold value (e.g., what counts as "tall")

## Semantics

Scalar adjectives have a free threshold variable:
- ⟦tall⟧ = λθ.λx. height(x) > θ
- ⟦short⟧ = λθ.λx. height(x) < θ

## Model Parameters

The paper uses α = 4 and C(u) = 2/3 × length(u) (Section 4.4).
Our discretized model uses α = 1 for the basic model and a linear
cost approximation for the cost-sensitive model.

## Structure

Model definitions and prediction theorems live in this single file.
Each theorem tests a specific claim from the paper, cited by section
and (where applicable) figure number. All predictions are verified
by `native_decide` — if the model changes, the build breaks.
-/

namespace RSA.LassiterGoodman2017

open RSA.Eval
open Core.Scale (Degree Threshold Degree.toNat Threshold.toNat
  deg thr allDegrees allThresholds)

-- ============================================================================
-- Domain: Heights and Thresholds (Discretized)
-- ============================================================================

/--
Discretized height values (in inches, scaled).

We use a discrete approximation to the continuous model in the paper.
Heights range from "short" (0) to "tall" (10) in discrete steps.
Now backed by the canonical `Degree 10` type with `LinearOrder` and `BoundedOrder`.
-/
abbrev Height := Degree 10

/--
Threshold values for "tall".

The threshold θ determines the cutoff: x is tall iff height(x) > θ.
Now backed by the canonical `Threshold 10` type.
-/
abbrev Threshold := Core.Scale.Threshold 10

-- ============================================================================
-- Utterances
-- ============================================================================

/-- Utterances about height -/
inductive Utterance where
  | tall    -- "x is tall"
  | short   -- "x is short"
  | silent  -- say nothing
  deriving Repr, DecidableEq, BEq, Fintype

-- ============================================================================
-- Semantics with Free Threshold Variable
-- ============================================================================

/--
Literal meaning of "tall" given a threshold.

⟦tall⟧(θ)(x) = 1 iff height(x) > θ

This captures the free-variable semantics from the paper (Eq. 21–22).
-/
def tallMeaning (θ : Threshold) (h : Height) : Bool :=
  h.toNat > θ.toNat

/--
Literal meaning of "short" given a threshold.

⟦short⟧(θ)(x) = 1 iff height(x) < θ
-/
def shortMeaning (θ : Threshold) (h : Height) : Bool :=
  h.toNat < θ.toNat

/--
Full meaning function: utterance × threshold → height → Bool
-/
def meaning (u : Utterance) (θ : Threshold) (h : Height) : Bool :=
  match u with
  | .tall => tallMeaning θ h
  | .short => shortMeaning θ h
  | .silent => true  -- Silent is always "true" (vacuously)

-- ============================================================================
-- Joint State: (Height, Threshold)
-- ============================================================================

/--
Joint state space: pairs of (Height, Threshold).

This is the space over which L1 reasons jointly.
-/
abbrev JointState := Height × Threshold

instance : Fintype JointState := inferInstance
instance : DecidableEq JointState := inferInstance
instance : BEq JointState := inferInstance

-- ============================================================================
-- Priors
-- ============================================================================

/--
Height prior: approximates a normal distribution centered at h5.

This models the reference class distribution (e.g., adult male heights).
The paper uses a continuous normal; we discretize.
-/
def heightPrior (h : Height) : ℚ :=
  match h.toNat with
  | 0 => 1    -- tails
  | 1 => 2
  | 2 => 5
  | 3 => 10
  | 4 => 15
  | 5 => 20   -- peak (mean)
  | 6 => 15
  | 7 => 10
  | 8 => 5
  | 9 => 2
  | _ => 1    -- tails

/--
Threshold prior: uniform over all thresholds.

The paper assumes uniform priors on semantic variables (Section 4.2):
"P_{L_{0/1}}(V) is thus uniform for all possible combinations of values
for the elements of V."
-/
def thresholdPrior : Threshold → ℚ := λ _ => 1

/--
Joint prior: P(h, θ) = P(h) × P(θ)

The paper assumes independence (Eq. 29).
-/
def jointPrior (state : JointState) : ℚ :=
  heightPrior state.1 * thresholdPrior state.2

-- ============================================================================
-- Utterance Costs (Full Paper Model)
-- ============================================================================

/--
Utterance costs from the full paper model.

The paper (Section 4.2, Eq. 23) includes utterance costs:
- C(tall) = C(short) = costWord (saying something has a cost)
- C(silent) = 0 (staying silent is free)

This creates the "pragmatic sweet spot" for thresholds.
-/
def utteranceCost (costWord : ℚ) : Utterance → ℚ
  | .tall => costWord
  | .short => costWord
  | .silent => 0

/-- Default word cost (calibrated to approximate exp(-α×C) behavior) -/
def defaultWordCost : ℚ := 1

-- ============================================================================
-- RSA Model with Threshold Inference
-- ============================================================================

/-- List of all utterances -/
def allUtterances : List Utterance := [.tall, .short, .silent]

/-- List of all heights -/
def allHeights : List Height := allDegrees 10

/-- List of all thresholds -/
def allThresholds : List Threshold := Core.Scale.allThresholds 10

/-- Run L0 for vague adjectives at a given threshold -/
def runL0 (u : Utterance) (θ : Threshold) : List (Height × ℚ) :=
  RSA.Eval.basicL0 allUtterances allHeights
    (λ utt h => boolToRat (meaning utt θ h)) (λ _ => 1) u

/-- Run S1 for vague adjectives at a given height and threshold -/
def runS1 (h : Height) (θ : Threshold) : List (Utterance × ℚ) :=
  RSA.Eval.basicS1 allUtterances allHeights
    (λ utt ht => boolToRat (meaning utt θ ht)) (λ _ => 1) 1 (λ _ => 0) h

/-- Run L1 joint distribution over (height, threshold).

The threshold θ is a semantic parameter, not a world variable.
The speaker at S1 knows both h and θ, and reasons about L0(h | u, θ)
which normalizes over heights for each fixed θ.

P_L1(h, θ | u) ∝ P(h) × P(θ) × P_S1(u | h, θ)

where S1 uses per-θ L0, matching the paper's Eq. 27–29. -/
def runL1_joint (u : Utterance) : List ((Height × Threshold) × ℚ) :=
  let pairs := allHeights.flatMap λ h => allThresholds.map λ θ => (h, θ)
  let scores := pairs.map λ (h, θ) =>
    let s1Dist := RSA.Eval.basicS1 allUtterances allHeights
      (λ utt ht => boolToRat (meaning utt θ ht)) heightPrior 1 (λ _ => 0) h
    let s1Score := RSA.Eval.getScore s1Dist u
    ((h, θ), heightPrior h * thresholdPrior θ * s1Score)
  RSA.Eval.normalize scores

/-- Run L1 marginal over heights -/
def runL1_world (u : Utterance) : List (Height × ℚ) :=
  RSA.Eval.marginalize (runL1_joint u) Prod.fst

/-- Run L1 marginal over thresholds -/
def runL1_interp (u : Utterance) : List (Threshold × ℚ) :=
  RSA.Eval.marginalize (runL1_joint u) Prod.snd

-- ============================================================================
-- Cost-Sensitive RSA (Full Paper Model)
-- ============================================================================

/--
Cost-sensitive S1: Full paper model with utterance costs.

P_{S1}(u|w,θ) ∝ P_{L0}(w|u,θ)^α × exp(-α × C(u))

Since we work with rationals (no exp), we approximate by using:
P_{S1}(u|w,θ) ∝ P_{L0}(w|u,θ) × (1 - C(u) × discountFactor)

where discountFactor controls how much cost affects speaker choice.
-/
def S1_withCost (cost : Utterance → ℚ) (discountFactor : ℚ)
    (θ : Threshold) (h : Height) : List (Utterance × ℚ) :=
  let scores := allUtterances.map λ u =>
    let l0Score := RSA.Eval.getScore (runL0 u θ) h
    let costPenalty := max 0 (1 - cost u * discountFactor)
    (u, l0Score * costPenalty)
  RSA.Eval.normalize scores

/-- L1 joint with cost-sensitive speaker -/
def L1_joint_withCost (cost : Utterance → ℚ) (discountFactor : ℚ)
    (u : Utterance) : List ((Height × Threshold) × ℚ) :=
  let pairs := allHeights.flatMap λ h => allThresholds.map λ θ => (h, θ)
  let scores := pairs.map λ (h, θ) =>
    let priorScore := heightPrior h * thresholdPrior θ
    let s1Score := RSA.Eval.getScore (S1_withCost cost discountFactor θ h) u
    ((h, θ), priorScore * s1Score)
  RSA.Eval.normalize scores

/-- L1 marginal over heights with cost-sensitive speaker -/
def L1_world_withCost (cost : Utterance → ℚ) (discountFactor : ℚ)
    (u : Utterance) : List (Height × ℚ) :=
  RSA.Eval.marginalize (L1_joint_withCost cost discountFactor u) Prod.fst

/-- L1 marginal over thresholds with cost-sensitive speaker -/
def L1_interp_withCost (cost : Utterance → ℚ) (discountFactor : ℚ)
    (u : Utterance) : List (Threshold × ℚ) :=
  RSA.Eval.marginalize (L1_joint_withCost cost discountFactor u) Prod.snd

-- ============================================================================
-- Computed Distributions (Basic Model)
-- ============================================================================

/-- L0 for "tall" at threshold t5 (middle threshold) -/
def l0_tall_t5 : List (Height × ℚ) := runL0 .tall (thr 5)

/-- L0 for "short" at threshold t5 -/
def l0_short_t5 : List (Height × ℚ) := runL0 .short (thr 5)

/-- S1 for height h8 (tall person) at threshold t5 -/
def s1_h8_t5 : List (Utterance × ℚ) := runS1 (deg 8) (thr 5)

/-- S1 for height h2 (short person) at threshold t5 -/
def s1_h2_t5 : List (Utterance × ℚ) := runS1 (deg 2) (thr 5)

/-- S1 for height h5 (borderline) at threshold t5 -/
def s1_h5_t5 : List (Utterance × ℚ) := runS1 (deg 5) (thr 5)

/-- L1 joint distribution over (height, threshold) given "tall" -/
def l1_joint_tall : List ((Height × Threshold) × ℚ) := runL1_joint .tall

/-- L1 marginal over heights given "tall" -/
def l1_height_tall : List (Height × ℚ) := runL1_world .tall

/-- L1 marginal over thresholds given "tall" -/
def l1_threshold_tall : List (Threshold × ℚ) := runL1_interp .tall

-- ============================================================================
-- Computed Distributions (Cost-Sensitive Model)
-- ============================================================================

/-- Cost function for vague adjectives -/
def vagueAdjectiveCost : Utterance → ℚ := utteranceCost defaultWordCost

/-- Discount factor controlling cost sensitivity (higher = stronger penalty) -/
def costDiscount : ℚ := 7/10

/-- S1 with costs for height h8 (tall person) at threshold t5 -/
def s1_cost_h8_t5 : List (Utterance × ℚ) :=
  S1_withCost vagueAdjectiveCost costDiscount (thr 5) (deg 8)

/-- S1 with costs for height h5 (borderline) at threshold t5 -/
def s1_cost_h5_t5 : List (Utterance × ℚ) :=
  S1_withCost vagueAdjectiveCost costDiscount (thr 5) (deg 5)

/-- L1 marginal over heights given "tall" (with costs) -/
def l1_height_tall_cost : List (Height × ℚ) :=
  L1_world_withCost vagueAdjectiveCost costDiscount .tall

/-- L1 marginal over thresholds given "tall" (with costs) -/
def l1_threshold_tall_cost : List (Threshold × ℚ) :=
  L1_interp_withCost vagueAdjectiveCost costDiscount .tall

-- ============================================================================
-- Sweet Spot Conditions (Section 4.3)
-- ============================================================================

/--
Conditions under which the pragmatic sweet spot exists.

The sweet spot (where middle thresholds beat both extremes) requires:
1. Non-trivial height prior (variance > 0)
2. Positive costs for speaking
3. Costs not so high that silence dominates

This structure captures the analytical conditions from Section 4.3.
-/
structure SweetSpotConditions where
  /-- Cost for producing an utterance (C > 0 for non-silent) -/
  utteranceCost : ℚ
  /-- Cost must be positive to penalize uninformative utterances -/
  cost_positive : utteranceCost > 0
  /-- The threshold where the sweet spot peaks -/
  peakThreshold : Threshold
  /-- Prior must assign non-zero probability to heights above and below peak -/
  prior_has_spread : Bool  -- simplified; could be more precise

-- ============================================================================
-- Context-Sensitivity (Section 4.2)
-- ============================================================================

/--
Height prior for a different reference class (e.g., basketball players).

The distribution is shifted right compared to the general population:
- General population: peak at h5 (average height)
- Basketball players: peak at h7 (taller on average)
-/
def basketballPrior (h : Height) : ℚ :=
  match h.toNat with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 5
  | 5 => 10
  | 6 => 15
  | 7 => 20   -- peak shifted to h7
  | 8 => 15
  | 9 => 10
  | _ => 5

/-- Run L1 joint for basketball scenario (shifted prior).

Same per-θ structure as `runL1_joint`, but with basketball height prior. -/
def runL1_joint_basketball (u : Utterance) : List ((Height × Threshold) × ℚ) :=
  let pairs := allHeights.flatMap λ h => allThresholds.map λ θ => (h, θ)
  let scores := pairs.map λ (h, θ) =>
    let s1Dist := RSA.Eval.basicS1 allUtterances allHeights
      (λ utt ht => boolToRat (meaning utt θ ht)) basketballPrior 1 (λ _ => 0) h
    let s1Score := RSA.Eval.getScore s1Dist u
    ((h, θ), basketballPrior h * thresholdPrior θ * s1Score)
  RSA.Eval.normalize scores

/-- L1 threshold distribution for "tall" with basketball prior -/
def l1_threshold_tall_basketball : List (Threshold × ℚ) :=
  RSA.Eval.marginalize (runL1_joint_basketball .tall) Prod.snd

/-- L1 height distribution for "tall" with basketball prior -/
def l1_height_tall_basketball : List (Height × ℚ) :=
  RSA.Eval.marginalize (runL1_joint_basketball .tall) Prod.fst

-- ============================================================================
-- Threshold vs Graded Semantics
-- ============================================================================

/--
Graded meaning: degree of "tall" as a function of height.

This represents the alternative graded semantics approach where
"tall" has degrees of truth directly, without threshold variables.
-/
def gradedTallness (h : Height) : ℚ :=
  -- Degree = proportion of thresholds below h
  -- With uniform threshold prior, this is h/10
  h.toNat / 10

/--
Marginalized threshold meaning: P(θ < h) with uniform prior.

This computes the probability that height h exceeds a randomly
chosen threshold, which equals the CDF of the threshold prior.
-/
def marginalizedThresholdMeaning (h : Height) : ℚ :=
  -- Count thresholds below h, divide by total thresholds
  let belowCount := (allThresholds.filter λ θ => h.toNat > θ.toNat).length
  belowCount / 10

/-- Graded meaning function -/
def gradedMeaning (u : Utterance) (h : Height) : ℚ :=
  match u with
  | .tall => gradedTallness h
  | .short => 1 - gradedTallness h
  | .silent => 1

/-- L1 for "tall" under graded semantics -/
def l1_height_tall_graded : List (Height × ℚ) :=
  RSA.Eval.basicL1 allUtterances allHeights
    gradedMeaning heightPrior 1 (λ _ => 0) .tall

-- ============================================================================
-- Section 4.2: Height and Threshold Inference
-- ============================================================================

/-- Given "x is tall", L1 infers x is probably taller than average (Fig. 5).

The paper: "the posterior distribution on x is shifted relative to the prior." -/
theorem tall_shifts_height_up :
    getScore l1_height_tall (deg 8) > getScore l1_height_tall (deg 2) := by
  native_decide

/-- Hearing "tall" shifts the posterior rightward (Fig. 5).

The upper tail (h ≥ 6) receives more probability in the posterior
than the prior assigns: prior upper tail = (15+10+5+2+1)/86 = 33/86. -/
theorem tall_concentrates_on_high_heights :
    getScore l1_height_tall (deg 6) +
    getScore l1_height_tall (deg 7) +
    getScore l1_height_tall (deg 8) +
    getScore l1_height_tall (deg 9) +
    getScore l1_height_tall (deg 10) > 33/86 := by
  native_decide

/-- Hearing "tall" assigns zero probability to the minimum height.

No matter what threshold the listener infers, h0 cannot be "tall"
because there is no threshold below 0. -/
theorem tall_rules_out_minimum_height :
    getScore l1_height_tall (deg 0) = 0 := by
  native_decide

/-- A tall person (h8) is more likely called "tall" than "short".
A short person (h2) is more likely called "short" than "tall". -/
theorem tall_short_contrast :
    getScore s1_h8_t5 .tall > getScore s1_h8_t5 .short ∧
    getScore s1_h2_t5 .short > getScore s1_h2_t5 .tall := by
  native_decide

-- ============================================================================
-- Section 4.3: Threshold Inference and the Sweet Spot
-- ============================================================================

/-- In the basic model without utterance costs, lower thresholds are
monotonically preferred because they make "tall" more likely true (Section 4.3).

The paper: without costs, "the speaker's observed choice to utter 'Al is tall'
can only be rationalized if it increases the probability of the true answer
considerably, and low values of θ_tall do not meet this requirement" — but
this rationalization requires costs. -/
theorem baseline_lowest_threshold_wins :
    getScore l1_threshold_tall (thr 0) > getScore l1_threshold_tall (thr 5) ∧
    getScore l1_threshold_tall (thr 5) > getScore l1_threshold_tall (thr 9) := by
  native_decide

/-- Very high thresholds (t9) have lower probability than middle thresholds (t5)
because the prior probability P(h > θ_high) is very low (Section 4.3).

The paper: "the strength of the dispreference generated by u's low prior
probability of truth outweighs the informativity preference." -/
theorem high_threshold_penalized_by_prior :
    getScore l1_threshold_tall (thr 9) < getScore l1_threshold_tall (thr 5) := by
  native_decide

/-- Given "tall", not all thresholds are equally likely.

Pragmatic reasoning resolves threshold uncertainty even though the prior
over thresholds is uniform (Section 4.2). -/
theorem threshold_posterior_nonuniform :
    getScore l1_threshold_tall (thr 0) ≠ getScore l1_threshold_tall (thr 5) := by
  native_decide

/-- Costs shift probability away from low thresholds toward higher ones,
capturing the informativity preference (Section 4.3): low thresholds
make "tall" uninformative, so speakers pay cost for nothing.

Measured as: the ratio P(t_high)/P(t_low) increases with costs. -/
theorem low_threshold_penalized_by_costs :
    getScore l1_threshold_tall_cost (thr 5) * getScore l1_threshold_tall (thr 0) >
    getScore l1_threshold_tall (thr 5) * getScore l1_threshold_tall_cost (thr 0) := by
  native_decide

/-- Costs reduce the gap between low and middle thresholds,
compressing the distribution toward the sweet spot (Section 4.3). -/
theorem costs_compress_threshold_distribution :
    (getScore l1_threshold_tall (thr 0) - getScore l1_threshold_tall (thr 5)) >
    (getScore l1_threshold_tall_cost (thr 0) - getScore l1_threshold_tall_cost (thr 5)) := by
  native_decide

/-- Costs shift probability mass from low thresholds toward higher ones (Section 4.3).

The ratio P(t9)/P(t0) is higher with costs than without. -/
theorem costs_increase_high_threshold_ratio :
    getScore l1_threshold_tall_cost (thr 9) * getScore l1_threshold_tall (thr 0) >
    getScore l1_threshold_tall (thr 9) * getScore l1_threshold_tall_cost (thr 0) := by
  native_decide

/-- Both forces from Section 4.3 are present in our model:
1. High θ penalized by prior (t9 < t5, even without costs)
2. Low θ penalized by costs (ratio shifts toward middle) -/
theorem both_forces_present :
    getScore l1_threshold_tall (thr 9) < getScore l1_threshold_tall (thr 5) ∧
    getScore l1_threshold_tall_cost (thr 5) * getScore l1_threshold_tall (thr 0) >
    getScore l1_threshold_tall (thr 5) * getScore l1_threshold_tall_cost (thr 0) := by
  native_decide

/-- The sweet spot must be bounded away from extremes (Section 4.3).

t5 beats t9 (prior effect) and costs push t5 up relative to t0. -/
theorem sweet_spot_bounded_away_from_extremes :
    getScore l1_threshold_tall (thr 5) > getScore l1_threshold_tall (thr 9) ∧
    getScore l1_threshold_tall_cost (thr 5) / getScore l1_threshold_tall_cost (thr 0) >
    getScore l1_threshold_tall (thr 5) / getScore l1_threshold_tall (thr 0) := by
  native_decide

-- ============================================================================
-- Section 4.4: Borderline Cases
-- ============================================================================

/-- Borderline cases have intermediate probability (Section 4.4).

The paper: "members of the set of clear positive cases of 'tall' get
very high probability, and the clear negative cases get very low
probability, and the cases in between — the 'borderline' cases —
receive intermediate levels of probability."

The posterior increases monotonically from clearly-not-tall (h1) through
borderline (h5), reflecting the rightward shift from the prior. -/
theorem borderline_has_intermediate_prob :
    getScore l1_height_tall (deg 5) > 0 ∧
    getScore l1_height_tall (deg 1) <
    getScore l1_height_tall (deg 3) ∧
    getScore l1_height_tall (deg 3) <
    getScore l1_height_tall (deg 5) := by
  native_decide

/-- The cost-sensitive model preserves the borderline gradient:
the posterior increases monotonically from clearly-not-tall to borderline. -/
theorem borderline_has_intermediate_prob_cost :
    getScore l1_height_tall_cost (deg 5) > 0 ∧
    getScore l1_height_tall_cost (deg 1) <
    getScore l1_height_tall_cost (deg 3) ∧
    getScore l1_height_tall_cost (deg 3) <
    getScore l1_height_tall_cost (deg 5) := by
  native_decide

/-- The cost-sensitive model still correctly infers tall heights from "tall". -/
theorem tall_shifts_height_up_cost :
    getScore l1_height_tall_cost (deg 8) > getScore l1_height_tall_cost (deg 2) := by
  native_decide

-- ============================================================================
-- Section 4.2: Context-Sensitivity
-- ============================================================================

/-!
The paper's main claim (Section 4.2) is that context-sensitivity of scalar
adjectives emerges from pragmatic inference, without stipulating different
meanings for different contexts.

The same semantics `⟦tall⟧ = λθ.λx. height(x) > θ` produces different
interpretations when the height prior P(h) varies by reference class.
Context-sensitivity is derived, not stipulated.
-/

/-- The interpretation of "tall" shifts with the reference class prior (Section 4.2).

When the prior shifts right (basketball players are taller on average),
the inferred threshold also shifts right. -/
theorem context_sensitivity_shifts_threshold :
    getScore l1_threshold_tall_basketball (thr 6) * getScore l1_threshold_tall (thr 3) >
    getScore l1_threshold_tall (thr 6) * getScore l1_threshold_tall_basketball (thr 3) := by
  native_decide

/-- Hearing "tall" about a basketball player suggests a taller height (Section 4.2).

"Al is a tall basketball player" implies Al is taller than
"Al is a tall man" (general population). -/
theorem context_sensitivity_shifts_height :
    getScore l1_height_tall_basketball (deg 8) > getScore l1_height_tall (deg 8) := by
  native_decide

/-- The identical meaning function is used for both contexts (Section 4.2).

For the general population, h5 is borderline tall.
For basketball players, h5 is clearly not tall (below their average).
The difference comes entirely from the prior. -/
theorem same_semantics_different_interpretation :
    getScore l1_height_tall_basketball (deg 5) < getScore l1_height_tall (deg 5) := by
  native_decide

-- ============================================================================
-- Section 5: The Sorites Paradox
-- ============================================================================

/-!
The sorites paradox arises from:
1. Clear case: "7-footers are tall" (accepted)
2. Tolerance: "If x is tall, then x - 1mm is tall" (each step accepted)
3. Absurd conclusion: "4-footers are tall" (rejected)

The paper (Section 5) explains this via probabilistic tolerance:
each tolerance step has high but not certain probability, so the
cumulative effect over many steps is significant.
-/

/-- Adjacent heights have similar probabilities: each step preserves
most of the probability (Section 5).

The sorites becomes compelling because each step seems individually
acceptable (> 75% preserved). -/
theorem sorites_tolerance_adjacent :
    let p7 := getScore l1_height_tall (deg 7)
    let p6 := getScore l1_height_tall (deg 6)
    let p5 := getScore l1_height_tall (deg 5)
    p6 > p7 * 3/4 ∧ p5 > p6 * 3/4 := by
  native_decide

/-- While each step preserves most probability (tolerance), the
cumulative effect is substantial (Section 5).

The paper: "the probability of the tolerance principle is less than 1,
and so when iterated enough times can lead to total probability less
than 0.5." -/
theorem sorites_accumulation :
    getScore l1_height_tall (deg 10) >
    5 * getScore l1_height_tall (deg 1) := by
  native_decide

/-- The sorites endpoints are clearly differentiated (Section 5).

Clear positive cases (h10) are much more probable than clear negative
cases (h1), and h1 is close to zero. -/
theorem sorites_clear_endpoints :
    getScore l1_height_tall (deg 10) > getScore l1_height_tall (deg 1) ∧
    getScore l1_height_tall (deg 1) < 1/100 := by
  native_decide

-- ============================================================================
-- Threshold vs Graded Semantics
-- ============================================================================

/-!
Threshold semantics (this paper) and graded semantics (e.g., fuzzy logic)
can be equivalent at L0 after marginalizing over thresholds, but diverge
at S1/L1 because RSA reasoning about which threshold the speaker intended
adds information beyond the marginalized meaning.
-/

/-- With a uniform prior over thresholds, the marginalized threshold
semantics equals graded semantics. -/
theorem threshold_graded_equivalence :
    (allHeights.map λ h => gradedTallness h == marginalizedThresholdMeaning h).all id = true := by
  native_decide

/-- The degree of tallness increases with height. -/
theorem graded_monotonic :
    gradedTallness (deg 3) < gradedTallness (deg 5) ∧
    gradedTallness (deg 5) < gradedTallness (deg 8) := by
  native_decide

/-- Every height has a non-trivial degree (except h0),
capturing the "no sharp boundary" property of graded semantics. -/
theorem graded_no_sharp_boundary :
    gradedTallness (deg 1) > 0 ∧
    gradedTallness (deg 1) < 1 ∧
    gradedTallness (deg 9) > 0 ∧
    gradedTallness (deg 9) < 1 := by
  native_decide

/-- At L1, threshold RSA and graded RSA diverge because threshold
semantics allows inference about the threshold variable. -/
theorem threshold_graded_rsa_diverge :
    getScore l1_height_tall (deg 7) ≠ getScore l1_height_tall_graded (deg 7) := by
  native_decide

/-- At the extremes, both threshold and graded models agree
that h10 is more likely "tall" than h1. -/
theorem threshold_graded_agree_extremes :
    getScore l1_height_tall (deg 10) > getScore l1_height_tall (deg 1) ∧
    getScore l1_height_tall_graded (deg 10) > getScore l1_height_tall_graded (deg 1) := by
  native_decide

end RSA.LassiterGoodman2017
