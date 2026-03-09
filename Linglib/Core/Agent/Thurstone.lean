import Linglib.Core.Agent.RationalAction
import Linglib.Core.Agent.NormalCDF
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Thurstone's Theory of Discriminal Processes @cite{luce-1959}

@cite{luce-1959} §2.D (pp. 53-60): @cite{thurstone-1927}'s Case V model of
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
the normal CDF `Φ(x · π/√3)`. The maximum absolute deviation between the two
is approximately 0.01. This means Thurstone's Case V is approximately a special
case of the Luce model:

  `P(a,b) ≈ 1/(1 + exp(-k(u(a) - u(b))))`

for `k = π / (σ√6)`. The logistic approximation is what makes the
connection to Luce's ratio-scale framework (§2.A) and hence to softmax (§2).

## Strong Stochastic Transitivity

Thurstone Case V satisfies strong stochastic transitivity: if `u(a) > u(b) > u(c)`,
then `P(a,c) > max(P(a,b), P(b,c))`. This is stronger than the weak stochastic
transitivity that Luce's axioms alone guarantee.
-/

namespace Core

open Real MeasureTheory BigOperators Set

-- ============================================================================
-- §2. Thurstone Case V
-- ============================================================================

/-- Thurstone's Case V model (@cite{thurstone-1927}; @cite{luce-1959}, §2.D).

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

-- ============================================================================
-- §4. Thurstone–Luce Connection
-- ============================================================================

/-!
## Thurstone Case V and the Luce Model

Set `d = u(a) - u(b)` and `k = π / (σ · √6)`. Then the exact identity:

  `d / (σ√2) = k · d · (√3/π)`

rewrites the Thurstone formula as:

  `P_T(a,b) = Φ(d / (σ√2)) = Φ(k·d · √3/π)`

Since `Φ(y · √3/π) ≈ logistic(y)` numerically (max error ~0.023 with
variance matching; see @cite{luce-1959} §2.D.2, Table 3), this gives:

  `P_T(a,b) ≈ logistic(k·d) = 1/(1 + exp(-k·(u(a) - u(b))))`

The constant `k = π/(σ√6)` arises from matching variances: the standard
logistic has variance `π²/3`, while the Thurstone difference distribution
(two i.i.d. N(0,σ²) draws) has variance `2σ²`. Setting `π²β²/3 = 2σ²`
gives `β = σ√6/π`, so `k = 1/β = π/(σ√6)`.

The Gumbel-Luce model (`GumbelLuce.lean`) gives **exactly** logistic(d/β)
by McFadden's theorem — no approximation. The Thurstone model gives
**exactly** Φ(d/(σ√2)). They agree up to `Φ ≈ logistic` which is a
purely numerical fact (~0.023 max error with variance matching, ~0.009
with the optimal constant 1.702).
-/

/-- The scaling constant connecting Thurstone and Luce:
    `k = π / (σ · √6)` so that `(u(a)-u(b))/(σ√2) = k·(u(a)-u(b))·(√3/π)`. -/
noncomputable def thurstoneLuceK (sigma : ℝ) : ℝ :=
  Real.pi / (sigma * Real.sqrt 6)

/-- **Thurstone–Luce identity** (@cite{luce-1959}, §2.D): the Thurstone
    choice probability equals `normalCDF` evaluated at the variance-matched
    Luce argument scaled by `√3/π`.

    `P_T(a,b) = Φ(d/(σ√2)) = Φ(k·d·√3/π)`

    where `k = π/(σ√6)` and `d = u(a) - u(b)`. Since `Φ(y·√3/π) ≈ logistic(y)`
    numerically, this gives `P_T(a,b) ≈ logistic(k·d)` — the Luce model.

    The approximation `Φ(y·√3/π) ≈ logistic(y)` has max error ~0.023
    (variance matching) and is a numerical fact without analytical proof. -/
theorem thurstone_luce_identity (m : ThurstoneCaseV Stimulus)
    (a b : Stimulus) :
    m.choiceProb a b =
    normalCDF (thurstoneLuceK m.sigma * (m.scale a - m.scale b) *
              (Real.sqrt 3 / Real.pi)) := by
  simp only [ThurstoneCaseV.choiceProb, thurstoneLuceK]
  congr 1
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [show (6 : ℝ) = 2 * 3 from by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  field_simp
  rw [h6]
  ring

end Core
