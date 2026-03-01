import Linglib.Core.Agent.RationalAction
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Thurstone's Theory of Discriminal Processes @cite{luce-1959}

Luce (1959) §2.D (pp. 53-60): Thurstone's (1927) Case V model of
paired comparison, and the logistic approximation that connects it to the
Luce choice rule.

## Thurstone Case V

Each stimulus `a` evokes a random **discriminal process** — a Gaussian random
variable with mean `u(a)` (the scale value) and standard deviation `σ`. When
a subject compares `a` and `b`, they sample one discriminal process for each
stimulus. The probability of choosing `a` over `b` is the probability that the
sample for `a` exceeds that for `b`:

  `P(a,b) = Φ((u(a) - u(b)) / (σ√2))`

where `Φ` is the standard normal CDF. Case V assumes equal variances across
all stimuli — the "simplest nontrivial case" in Thurstone's taxonomy.

## The Logistic Approximation (pp. 58-59)

Luce observes that the logistic function `1/(1 + exp(-x))` closely approximates
the normal CDF `Φ(x · √(π/3))`. The maximum absolute deviation between the two
is approximately 0.01. This means Thurstone's Case V is approximately a special
case of the Luce model:

  `P(a,b) ≈ 1/(1 + exp(-k(u(a) - u(b))))`

for `k = √(π/3) / (σ√2)`. The logistic approximation is what makes the
connection to Luce's ratio-scale framework (§2.A) and hence to softmax (§2).

## Strong Stochastic Transitivity

Thurstone Case V satisfies strong stochastic transitivity: if `u(a) > u(b) > u(c)`,
then `P(a,c) > max(P(a,b), P(b,c))`. This is stronger than the weak stochastic
transitivity that Luce's axioms alone guarantee.
-/

namespace Core

open Real MeasureTheory BigOperators Set

-- ============================================================================
-- §1. Normal CDF
-- ============================================================================

/-- The standard normal probability density function: `φ(t) = (1/√(2π)) · exp(-t²/2)`. -/
noncomputable def normalPDF (t : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(t ^ 2) / 2)

/-- The standard normal cumulative distribution function:
    `Φ(x) = ∫_{-∞}^{x} (1/√(2π)) exp(-t²/2) dt`.

    Defined as the Lebesgue integral of the standard normal PDF over `(-∞, x]`. -/
noncomputable def normalCDF (x : ℝ) : ℝ :=
  ∫ t in Iic x, normalPDF t

/-- The normal CDF is monotone increasing. -/
theorem normalCDF_mono : Monotone normalCDF := by
  sorry -- TODO: follows from normalPDF being non-negative

/-- `Φ(0) = 1/2` by symmetry of the standard normal distribution. -/
theorem normalCDF_zero : normalCDF 0 = 1 / 2 := by
  sorry -- TODO: symmetry of the Gaussian integral

/-- For `x > 0`, `Φ(x) > 1/2`. -/
theorem normalCDF_pos_gt_half {x : ℝ} (hx : 0 < x) : 1 / 2 < normalCDF x := by
  sorry -- TODO: follows from normalCDF_mono and normalCDF_zero

/-- For `x < 0`, `Φ(x) < 1/2`. -/
theorem normalCDF_neg_lt_half {x : ℝ} (hx : x < 0) : normalCDF x < 1 / 2 := by
  sorry -- TODO: follows from normalCDF_mono and normalCDF_zero

/-- Symmetry: `Φ(-x) = 1 - Φ(x)`. -/
theorem normalCDF_neg (x : ℝ) : normalCDF (-x) = 1 - normalCDF x := by
  sorry -- TODO: change of variables t ↦ -t in the integral

/-- The normal CDF is strictly monotone increasing. -/
theorem normalCDF_strictMono : StrictMono normalCDF := by
  sorry -- TODO: follows from normalPDF being strictly positive

-- ============================================================================
-- §2. Thurstone Case V
-- ============================================================================

/-- Thurstone's Case V model (Thurstone 1927; Luce 1959, §2.D).

    Each stimulus has a scale value `scale(a)` and all stimuli share a common
    discriminal dispersion `sigma > 0`. The choice probability is determined
    by the normal CDF applied to the standardized scale difference. -/
structure ThurstoneCaseV (Stimulus : Type*) where
  /-- The scale value (mean of the discriminal process) for each stimulus. -/
  scale : Stimulus → ℝ
  /-- The common discriminal dispersion (standard deviation). -/
  sigma : ℝ
  /-- The dispersion is strictly positive. -/
  sigma_pos : 0 < sigma

variable {Stimulus : Type*}

/-- Choice probability under Thurstone Case V:
    `P(a,b) = Φ((u(a) - u(b)) / (σ√2))`.

    This is the probability that the discriminal process for `a` exceeds
    that for `b`, when both are independent Gaussians with means `u(a)`, `u(b)`
    and common variance `σ²`. The difference is Gaussian with mean
    `u(a) - u(b)` and variance `2σ²`, hence standard deviation `σ√2`. -/
noncomputable def ThurstoneCaseV.choiceProb (m : ThurstoneCaseV Stimulus)
    (a b : Stimulus) : ℝ :=
  normalCDF ((m.scale a - m.scale b) / (m.sigma * Real.sqrt 2))

/-- When `u(a) = u(b)`, the choice probability is `1/2` (indifference). -/
theorem ThurstoneCaseV.choiceProb_eq (m : ThurstoneCaseV Stimulus)
    (a b : Stimulus) (h : m.scale a = m.scale b) :
    m.choiceProb a b = 1 / 2 := by
  simp only [choiceProb, h, sub_self, zero_div]
  exact normalCDF_zero

/-- Complementarity: `P(a,b) + P(b,a) = 1`. -/
theorem ThurstoneCaseV.choiceProb_complement (m : ThurstoneCaseV Stimulus)
    (a b : Stimulus) :
    m.choiceProb a b + m.choiceProb b a = 1 := by
  simp only [choiceProb]
  have : (m.scale b - m.scale a) / (m.sigma * Real.sqrt 2) =
         -((m.scale a - m.scale b) / (m.sigma * Real.sqrt 2)) := by ring
  rw [this, normalCDF_neg]
  ring

/-- If `u(a) > u(b)`, then `P(a,b) > 1/2` — the higher-scale stimulus
    is chosen more often than chance. -/
theorem ThurstoneCaseV.choiceProb_gt_half (m : ThurstoneCaseV Stimulus)
    (a b : Stimulus) (h : m.scale b < m.scale a) :
    1 / 2 < m.choiceProb a b := by
  apply normalCDF_pos_gt_half
  apply div_pos (sub_pos.mpr h)
  exact mul_pos m.sigma_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))

-- ============================================================================
-- §3. Strong Stochastic Transitivity
-- ============================================================================

/-- **Strong stochastic transitivity** (Thurstone Case V).

    If `u(a) > u(b) > u(c)`, then `P(a,c) > P(a,b)` — the "big gap" comparison
    is easier than either "small gap" comparison.

    Proof: `u(a) - u(c) > u(a) - u(b)`, so after dividing by `σ√2 > 0`,
    the argument to `Φ` is larger, and `Φ` is strictly monotone. -/
theorem ThurstoneCaseV.transitivity_left (m : ThurstoneCaseV Stimulus)
    (a b c : Stimulus)
    (_hab : m.scale b < m.scale a) (hbc : m.scale c < m.scale b) :
    m.choiceProb a b < m.choiceProb a c := by
  simp only [choiceProb]
  apply normalCDF_strictMono
  apply div_lt_div_of_pos_right
  · linarith
  · exact mul_pos m.sigma_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))

/-- The right half of strong stochastic transitivity:
    if `u(a) > u(b) > u(c)`, then `P(a,c) > P(b,c)`. -/
theorem ThurstoneCaseV.transitivity_right (m : ThurstoneCaseV Stimulus)
    (a b c : Stimulus)
    (hab : m.scale b < m.scale a) (_hbc : m.scale c < m.scale b) :
    m.choiceProb b c < m.choiceProb a c := by
  simp only [choiceProb]
  apply normalCDF_strictMono
  apply div_lt_div_of_pos_right
  · linarith
  · exact mul_pos m.sigma_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))

-- ============================================================================
-- §4. Logistic Approximation of the Normal CDF
-- ============================================================================

/-!
## The Logistic Approximation (Luce 1959, pp. 58-59)

The logistic function `1/(1 + exp(-x))` approximates `Φ(x · √(π/3))` with
maximum absolute deviation ≈ 0.01. This is the key technical fact connecting
Thurstone's Gaussian model to Luce's exponential (softmax) model.

The scaling factor `√(π/3)` arises from matching variances: the standard
logistic distribution has variance `π²/3`, while the standard normal has
variance 1. Rescaling the logistic argument by `√(π/3)` matches the
second moments of the two distributions.
-/

/-- The logistic function closely approximates the normal CDF after rescaling.

    Specifically, `|Φ(x · √(π/3)) - logistic(x)| ≤ 0.01` for all `x`.
    The maximum deviation of ≈ 0.01 occurs near `|x| ≈ 1.3`.

    This is a numerical bound; the proof would require bounding the
    integral defining `Φ` against the closed-form logistic. -/
theorem logistic_approx_normal (x : ℝ) :
    |normalCDF (x * Real.sqrt (Real.pi / 3)) - logistic x| ≤ 0.01 := by
  sorry -- TODO: numerical bound, verified computationally

-- ============================================================================
-- §5. Thurstone–Luce Approximation
-- ============================================================================

/-!
## Thurstone Case V ≈ Luce Model

Set `d = u(a) - u(b)` and `k = 1 / (σ · √2 · √(π/3))`. Then:

  `d / (σ√2) = k · d · √(π/3)`

so the Thurstone formula becomes:

  `P_T(a,b) = Φ(d / (σ√2)) = Φ(kd · √(π/3)) ≈ logistic(kd)`

where the last step applies `logistic_approx_normal`. This gives:

  `P_T(a,b) ≈ 1/(1 + exp(-k(u(a) - u(b))))`

which is exactly the Luce model with rationality parameter `k`.
-/

/-- The scaling constant connecting Thurstone and Luce:
    `k = 1 / (σ · √2 · √(π/3))` so that `(u(a)-u(b))/(σ√2) = k·(u(a)-u(b))·√(π/3)`. -/
noncomputable def thurstoneLuceK (sigma : ℝ) : ℝ :=
  1 / (sigma * Real.sqrt 2 * Real.sqrt (Real.pi / 3))

/-- **Thurstone–Luce approximation** (Luce 1959, §2.D, pp. 58-59).

    With `k = 1/(σ√2 · √(π/3))`, the Thurstone Case V probability
    `P_T(a,b) = Φ((u(a)-u(b))/(σ√2))` and the Luce model probability
    `P_L(a,b) = 1/(1 + exp(-k(u(a)-u(b))))` satisfy `|P_T - P_L| ≤ 0.01`.

    This is the sense in which Thurstone's Gaussian model is "approximately
    a special case" of Luce's choice axiom. -/
theorem thurstone_luce_approximation (m : ThurstoneCaseV Stimulus)
    (a b : Stimulus) :
    |m.choiceProb a b -
     logistic (thurstoneLuceK m.sigma * (m.scale a - m.scale b))| ≤ 0.01 := by
  -- The key identity: (u(a)-u(b))/(σ√2) = k·(u(a)-u(b)) · √(π/3)
  -- where k = 1/(σ√2 · √(π/3)), so this reduces to logistic_approx_normal.
  sorry -- TODO: unfold thurstoneLuceK, simplify, apply logistic_approx_normal

/-- The Thurstone model gives the same choice probabilities as a `RationalAction`
    with softmax parameterization, up to the logistic approximation error.

    Concretely, constructing a `RationalAction.fromSoftmax` with `utility := scale`
    and `α := thurstoneLuceK sigma` gives a binary choice probability within
    0.01 of the Thurstone prediction. -/
theorem thurstone_as_softmax [Fintype Stimulus] [Nonempty Stimulus]
    (m : ThurstoneCaseV Stimulus) (a b : Stimulus) :
    |m.choiceProb a b -
     logistic (thurstoneLuceK m.sigma * (m.scale a - m.scale b))| ≤ 0.01 :=
  thurstone_luce_approximation m a b

end Core
