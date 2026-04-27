import Linglib.Core.Agent.RationalAction
import Linglib.Core.Probability.Gaussian
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

-- ============================================================================
-- §5. Luce–Thurstone Incompatibility for n ≥ 3
-- ============================================================================

/-!
## Theorem 7: Luce and Thurstone Diverge for Three or More Alternatives

@cite{luce-1959} Theorem 7 (§2.D.3): for pairwise comparisons (n = 2),
the Luce and Thurstone models are approximately equivalent
(`thurstone_luce_identity`). For n ≥ 3 alternatives, they are
**fundamentally incompatible**: no independent Thurstone discriminal
processes can generate both the "choose best" and "choose worst"
probabilities predicted by the Luce model.

The proof has two steps:

1. **Thurstone integral identity**: For independent discriminal processes,
   `P_best(x) - P_worst(x) = P(x,y) + P(x,z) - 1` (expanding the
   product of CDFs).

2. **Algebraic contradiction**: Under axiom 1, `P_best(x) = v(x)/Σv`
   and `P_worst(x) = (1/v(x))/Σ(1/v)`. Setting the axiom 1 difference
   equal to `P(x,y) + P(x,z) - 1` forces `P(x,y)·P(y,x)·P(z,x) = 0`,
   contradicting non-degeneracy.

The algebraic core (step 2) is formalized below.
-/

/-- **Luce–Thurstone incompatibility** (@cite{luce-1959}, Theorem 7):
    for three alternatives with positive Luce scales, the axiom 1
    "best-worst difference" does NOT equal `P(x,y) + P(x,z) - 1`
    (the value predicted by independent Thurstone processes).

    Specifically, axiom 1 gives:
    - `P_best(0) = v₀ / (v₀ + v₁ + v₂)`
    - `P_worst(0) = v₁v₂ / (v₀v₁ + v₀v₂ + v₁v₂)`
    - `P(0,1) + P(0,2) - 1 = v₀/(v₀+v₁) + v₀/(v₀+v₂) - 1`

    If these are equal (as the Thurstone integral identity requires),
    and `P(0,1) + P(0,2) ≠ 1` (Luce's hypothesis ii, equivalent to
    `v₀² ≠ v₁v₂`), then `v₀v₁v₂ = 0`, contradicting positivity.

    The proof clears denominators, factors out `(v₀² - v₁v₂)`, and
    shows the remaining factor is `-v₀v₁v₂ ≠ 0`. -/
theorem luce_thurstone7 (v : Fin 3 → ℝ) (hv : ∀ i, 0 < v i)
    (h_nd : v 0 / (v 0 + v 1) + v 0 / (v 0 + v 2) ≠ 1)
    (h : v 0 / (v 0 + v 1 + v 2) -
         v 1 * v 2 / (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) =
         v 0 / (v 0 + v 1) + v 0 / (v 0 + v 2) - 1) :
    False := by
  have h0 := hv 0; have h1 := hv 1; have h2 := hv 2
  have h01 : (0 : ℝ) < v 0 + v 1 := by linarith
  have h02 : (0 : ℝ) < v 0 + v 2 := by linarith
  have h012 : (0 : ℝ) < v 0 + v 1 + v 2 := by linarith
  have hq : (0 : ℝ) < v 0 * v 1 + v 0 * v 2 + v 1 * v 2 := by nlinarith
  -- Both sides factor through (v₀² - v₁v₂):
  --   RHS = (v₀² - v₁v₂) / ((v₀+v₁)(v₀+v₂))
  --   LHS = (v₀² - v₁v₂)(v₁+v₂) / ((v₀+v₁+v₂)(v₀v₁+v₀v₂+v₁v₂))
  have h_rhs : v 0 / (v 0 + v 1) + v 0 / (v 0 + v 2) - 1 =
      (v 0 ^ 2 - v 1 * v 2) / ((v 0 + v 1) * (v 0 + v 2)) := by
    field_simp; ring
  have h_lhs : v 0 / (v 0 + v 1 + v 2) -
      v 1 * v 2 / (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) =
      (v 0 ^ 2 - v 1 * v 2) * (v 1 + v 2) /
      ((v 0 + v 1 + v 2) * (v 0 * v 1 + v 0 * v 2 + v 1 * v 2)) := by
    field_simp; ring
  -- h_nd implies v₀² ≠ v₁v₂
  have h_sq_ne : v 0 ^ 2 - v 1 * v 2 ≠ 0 := by
    intro heq
    apply h_nd
    have : v 0 / (v 0 + v 1) + v 0 / (v 0 + v 2) - 1 = 0 := by rw [h_rhs, heq, zero_div]
    linarith
  -- Clear denominators
  rw [h_lhs, h_rhs] at h
  rw [div_eq_div_iff (mul_pos h012 hq |>.ne') (mul_pos h01 h02 |>.ne')] at h
  -- Cancel (v₀² - v₁v₂) from both sides
  have h5 : (v 1 + v 2) * ((v 0 + v 1) * (v 0 + v 2)) =
      (v 0 + v 1 + v 2) * (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) := by
    have h' : (v 0 ^ 2 - v 1 * v 2) *
              ((v 1 + v 2) * ((v 0 + v 1) * (v 0 + v 2))) =
              (v 0 ^ 2 - v 1 * v 2) *
              ((v 0 + v 1 + v 2) * (v 0 * v 1 + v 0 * v 2 + v 1 * v 2)) := by
      linarith
    exact mul_left_cancel₀ h_sq_ne h'
  -- (v₁+v₂)(v₀+v₁)(v₀+v₂) - (v₀+v₁+v₂)(v₀v₁+v₀v₂+v₁v₂) = -v₀v₁v₂
  have h6 : (v 1 + v 2) * ((v 0 + v 1) * (v 0 + v 2)) -
      (v 0 + v 1 + v 2) * (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) =
      -(v 0 * v 1 * v 2) := by ring
  -- From h5: v₀v₁v₂ = 0, but v₀v₁v₂ > 0. Contradiction.
  linarith [mul_pos (mul_pos h0 h1) h2]

/-- **Luce–Thurstone incompatibility (general)**: the n = 3 result extends
    to any n ≥ 3 alternatives by restricting to a 3-element subset.

    By IIA (Luce's axiom 1), the pairwise probabilities `P(i,j) = vᵢ/(vᵢ+vⱼ)`
    are the same regardless of choice set. The Thurstone integral identity
    only needs to hold for **one** triple `{i, j, k}` to derive a
    contradiction. So the incompatibility between Luce and independent
    Thurstone processes holds whenever n ≥ 3 and any non-degenerate
    triple exists.

    This is why Luce states Theorem 7 for |T| = 3 — the general case
    follows immediately from IIA + the base case. -/
theorem luce_thurstone_incompatible {n : ℕ}
    (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    -- Three distinct alternatives
    (i j k : Fin n) (_hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k)
    -- Non-degeneracy for this triple (Luce's hypothesis ii)
    (h_nd : v i / (v i + v j) + v i / (v i + v k) ≠ 1)
    -- Thurstone integral identity for this triple
    (h_int : v i / (v i + v j + v k) -
             v j * v k / (v i * v j + v i * v k + v j * v k) =
             v i / (v i + v j) + v i / (v i + v k) - 1) :
    False :=
  luce_thurstone7 ![v i, v j, v k]
    (by intro x; fin_cases x <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> exact hv _)
    (by simp [Matrix.cons_val_zero, Matrix.cons_val_one]; exact h_nd)
    (by simp [Matrix.cons_val_zero, Matrix.cons_val_one]; exact h_int)

end Core
