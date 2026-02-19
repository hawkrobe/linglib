import Linglib.Core.Scale
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Prod

/-!
# Lassiter & Goodman (2017) -- Threshold RSA for Vague Adjectives

"Adjectival vagueness in a Bayesian model of interpretation"
Synthese 194:3801-3836

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

## Status

RSA evaluation infrastructure (basicL0, basicL1, basicS1, getScore,
normalize, marginalize, boolToRat) has been removed. Domain types, meaning
functions, priors, cost structure, graded semantics, and algebraic properties
are preserved. RSA computation stubs and prediction theorems remain with
`sorry` for future reimplementation.
-/

namespace RSA.LassiterGoodman2017

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
instance : NeZero (10 : Nat) := ⟨by omega⟩
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

This captures the free-variable semantics from the paper (Eq. 21-22).
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
-- Lists
-- ============================================================================

/-- List of all utterances -/
def allUtterances : List Utterance := [.tall, .short, .silent]

/-- List of all heights -/
def allHeights : List Height := allDegrees 10

/-- List of all thresholds -/
def allThresholds : List Threshold := Core.Scale.allThresholds 10

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

/-- The degree of tallness increases with height. -/
theorem graded_monotonic :
    gradedTallness (deg 3) < gradedTallness (deg 5) ∧
    gradedTallness (deg 5) < gradedTallness (deg 8) := by
  sorry

/-- Every height has a non-trivial degree (except h0),
capturing the "no sharp boundary" property of graded semantics. -/
theorem graded_no_sharp_boundary :
    gradedTallness (deg 1) > 0 ∧
    gradedTallness (deg 1) < 1 ∧
    gradedTallness (deg 9) > 0 ∧
    gradedTallness (deg 9) < 1 := by
  sorry

end RSA.LassiterGoodman2017
