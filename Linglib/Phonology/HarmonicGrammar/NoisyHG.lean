import Linglib.Phonology.Constraints.Defs
import Linglib.Core.Probability.RandomUtility
import Linglib.Core.Probability.LogitChoice

/-!
# Noisy Harmonic Grammar and Normal MaxEnt
[boersma-pater-2016] [flemming-2021]

Noisy HG ([boersma-pater-2016]) adds i.i.d. Gaussian noise N(0,σ²) to
each constraint weight before evaluation. For binary choice between
candidates a and b, the harmony score difference H(a)−H(b) becomes a
Gaussian random variable with variance σ² · Σⱼ(cⱼ(a)−cⱼ(b))² — the noise
is **context-dependent**, scaling with squared violation differences.

Normal MaxEnt ([flemming-2021]) instead adds i.i.d. Gaussian noise
N(0,ε²) directly to candidate scores, giving a constant noise standard
deviation σ_d = ε√2 for binary choice.

Both are instances of the Gaussian random utility model (`Core.gaussianChoiceProb`,
the probit choice rule) — the Gaussian sibling of softmax. They ground directly in
that pure-math fact, not in Thurstone's psychophysics: Noisy HG and Thurstone Case V
are sibling applications of the same probit RUM, neither depending on the other.

A grammar here is a constraint set `con : CON C n` and a weight vector `w : Fin n → ℝ`
(from `Constraints.Defs`); there is no weighted-constraint record. Violation-difference
quantities (`violationDiffSqSum`, `nhgCovariance`) read only `con`; harmony quantities
read `con` and `w`.

## MaxEnt logit-harmony identity

For classical MaxEnt (Gumbel noise → softmax), the log-odds ratio between
any two candidates equals their harmony score difference:

  `log(P(a)/P(b)) = H(a) − H(b)`

This implies **logit uniformity** ([flemming-2021] §5.1, eq (10)): adding one
violation of constraint j changes the logit by exactly −wⱼ, regardless
of the violation profile elsewhere. NHG lacks this property because its
noise variance σ_d depends on the violation profile.
-/

namespace HarmonicGrammar


open Core Real Constraints

variable {C : Type*} {n : Nat}

-- ============================================================================
-- § 1: NHG Noise Variance
-- ============================================================================

/-- Sum of squared violation differences between two candidates.
    This determines the NHG noise variance: σ_d² = σ² · violationDiffSqSum. -/
noncomputable def violationDiffSqSum (con : CON C n) (a b : C) : ℝ :=
  ∑ i, ((con i a : ℝ) - (con i b : ℝ)) ^ 2

/-- Sum of squared violation differences (ℚ, computable).
    Use this for concrete examples with `decide`. -/
def violationDiffSqSumQ (con : CON C n) (a b : C) : ℚ :=
  ∑ i, ((con i a : ℚ) - (con i b : ℚ)) ^ 2

/-- NHG noise standard deviation for binary choice:
    σ_d = σ · √(Σⱼ (cⱼ(a) − cⱼ(b))²).

    The noise is **context-dependent**: it scales with the violation
    difference profile, not just the per-weight noise σ. -/
noncomputable def nhgSigmaD (con : CON C n) (sigma : ℝ) (a b : C) : ℝ :=
  sigma * Real.sqrt (violationDiffSqSum con a b)

-- ============================================================================
-- § 2: NHG binary choice (Gaussian random utility model)
-- ============================================================================

/-- **NHG binary choice probability** ([flemming-2021]):
    `P(a ≻ b) = Φ((H(a) − H(b)) / σ_d)`.

    Noisy HG is the Gaussian random utility model (`gaussianChoiceProb`, the
    probit choice rule) applied to the harmony gap, with the context-dependent
    NHG noise `σ_d = σ·√(Σⱼ(cⱼ(a)−cⱼ(b))²)` (`nhgSigmaD`). It grounds directly
    in the Gaussian RUM — *not* through Thurstone's psychophysics. -/
noncomputable def nhgChoiceProb (con : CON C n) (w : Fin n → ℝ) (sigma : ℝ) (a b : C) : ℝ :=
  gaussianChoiceProb (harmonyScore con w a - harmonyScore con w b)
    (nhgSigmaD con sigma a b)

/-- NHG choice probability in closed form: `Φ((H(a) − H(b)) / σ_d)`
    ([flemming-2021] eq (15)). -/
theorem nhg_choiceProb_eq (con : CON C n) (w : Fin n → ℝ) (sigma : ℝ) (a b : C) :
    nhgChoiceProb con w sigma a b =
    normalCDF ((harmonyScore con w a - harmonyScore con w b) /
               nhgSigmaD con sigma a b) := by
  simp only [nhgChoiceProb, gaussianChoiceProb]

-- ============================================================================
-- § 3: Normal MaxEnt
-- ============================================================================

/-- Normal MaxEnt noise standard deviation: σ_d = ε√2 (constant).

    When noise is added i.i.d. N(0,ε²) to each candidate score, the
    difference of two candidates is N(H(a)−H(b), 2ε²), giving σ_d = ε√2
    regardless of the violation profile. This is the key distinction
    from NHG, where σ_d varies by context. -/
noncomputable def normalMaxEntSigmaD (epsilon : ℝ) : ℝ :=
  epsilon * Real.sqrt 2

/-- **Normal MaxEnt binary choice probability** ([flemming-2021]):
    `P(a ≻ b) = Φ((H(a) − H(b)) / (ε√2))`.

    Like NHG, the Gaussian random utility model (`gaussianChoiceProb`) applied
    to the harmony gap — but with the *constant* noise `σ_d = ε√2`
    (`normalMaxEntSigmaD`) rather than NHG's context-dependent `σ_d`. -/
noncomputable def normalMaxEntChoiceProb (con : CON C n) (w : Fin n → ℝ)
    (epsilon : ℝ) (a b : C) : ℝ :=
  gaussianChoiceProb (harmonyScore con w a - harmonyScore con w b)
    (normalMaxEntSigmaD epsilon)

/-- Normal MaxEnt choice probability in closed form: `Φ((H(a) − H(b)) / (ε√2))`
    ([flemming-2021] eq (17)). -/
theorem normalMaxEnt_choiceProb_eq (con : CON C n) (w : Fin n → ℝ)
    (epsilon : ℝ) (a b : C) :
    normalMaxEntChoiceProb con w epsilon a b =
    normalCDF ((harmonyScore con w a - harmonyScore con w b) /
               normalMaxEntSigmaD epsilon) := by
  simp only [normalMaxEntChoiceProb, gaussianChoiceProb]

-- ============================================================================
-- § 4: MaxEnt Logit-Harmony Identity
-- ============================================================================

/-- **Logit uniformity** (MaxEnt diagnostic; [flemming-2021] §5.1):
    for softmax with α = 1, the log-odds between any two alternatives
    equals their score difference. Hence changing one score by −w
    changes the log-odds by exactly −w, regardless of context.

    This property characterizes MaxEnt among stochastic HG variants.
    NHG lacks it because its noise variance σ_d depends on the violation
    profile (see `nhgSigmaD`).

    See also `maxent_logit_as_finsum` (Separability.lean) for the
    Fin-indexed decomposition, and `me_predicts_hz` for the consequence
    that independent violation differences yield HZ's generalization. -/
theorem logit_uniformity {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) (a b : ι) :
    log (softmax s a / softmax s b) = s a - s b := by
  rw [log_softmax_odds]

/-- **MaxEnt logit-harmony identity**: the log-odds ratio between two
    candidates equals their harmony score difference.

    `log(P(a)/P(b)) = H(a) − H(b)`

    Instantiation of `logit_uniformity` with harmony scores. -/
theorem maxent_logit_harmony [Fintype C] [Nonempty C]
    (con : CON C n) (w : Fin n → ℝ) (a b : C) :
    log (softmax (harmonyScore con w) a /
         softmax (harmonyScore con w) b) =
    harmonyScore con w a - harmonyScore con w b :=
  logit_uniformity (harmonyScore con w) a b

/-- **Ratio independence** (IIA for MaxEnt): the probability ratio between
    two candidates depends only on their own harmony scores.

    `P(a)/P(b) = exp(H(a) − H(b))`

    Adding or removing other candidates from the competition doesn't
    change the ratio. Corollary of `softmax_odds` with α = 1. -/
theorem maxent_iia [Fintype C] [Nonempty C]
    (con : CON C n) (w : Fin n → ℝ) (a b : C) :
    softmax (harmonyScore con w) a /
    softmax (harmonyScore con w) b =
    exp (harmonyScore con w a - harmonyScore con w b) := by
  rw [softmax_odds]

-- ============================================================================
-- § 5: Harmony Difference Decomposition
-- ============================================================================

/-- **Harmony difference decomposition**: the harmony score difference
    equals the negated weighted sum of violation differences.

    `H(a) − H(b) = −Σⱼ wⱼ · (cⱼ(a) − cⱼ(b))`

    This is the bridge between abstract harmony scores and the constraint
    violation patterns used in empirical analyses (e.g., French schwa). -/
theorem harmonyScore_diff (con : CON C n) (w : Fin n → ℝ) (a b : C) :
    harmonyScore con w a - harmonyScore con w b =
    -∑ i, w i * ((con i a : ℝ) - (con i b : ℝ)) := by
  rw [harmonyScore_eq_neg_sum, harmonyScore_eq_neg_sum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

-- ============================================================================
-- § 6: Censored NHG ([flemming-2021] §7.3)
-- ============================================================================

/-- Censored weight: noise is clamped so weights never go negative.

    In censored NHG, the noisy weight is `max(0, w + n)` where `n ~ N(0,σ²)`.
    This prevents negative weights (which would reverse constraint preferences)
    and makes the effective noise variance depend on the weight magnitude:
    constraints with larger weights are less affected by censoring. -/
noncomputable def censoredWeight (w n : ℝ) : ℝ := max 0 (w + n)

/-- Censored weights are non-negative by construction. -/
theorem censoredWeight_nonneg (w n : ℝ) : 0 ≤ censoredWeight w n :=
  le_max_left 0 _

/-- Censored weights are monotone in the underlying weight. -/
theorem censoredWeight_mono_weight {w₁ w₂ n : ℝ} (hw : w₁ ≤ w₂) :
    censoredWeight w₁ n ≤ censoredWeight w₂ n :=
  max_le_max_left 0 (by linarith)

/-- **Weight sensitivity** ([flemming-2021] §7.3): censoring is
    non-trivial — different weights produce different censored values
    for some noise realization.

    The witness is `n = -w₁`: this zeroes out `w₁` but leaves `w₂ > 0`. -/
theorem censored_nhg_weight_sensitivity (w₁ w₂ : ℝ) (hw : w₁ < w₂) :
    ∃ n : ℝ, censoredWeight w₁ n ≠ censoredWeight w₂ n := by
  use -w₁
  simp only [censoredWeight, add_neg_cancel, max_self]
  rw [show w₂ + -w₁ = w₂ - w₁ from rfl]
  have h_pos : 0 < w₂ - w₁ := sub_pos.mpr hw
  rw [max_eq_right (le_of_lt h_pos)]
  exact ne_of_lt h_pos

-- ============================================================================
-- § 7: Multi-Candidate NHG Covariance
-- ============================================================================

/-- NHG noise covariance between two score differences relative to a
    reference candidate `a`:

    `Cov(ε_b − ε_a, ε_c − ε_a) = σ² · Σₖ (cₖ(b) − cₖ(a)) · (cₖ(c) − cₖ(a))`

    When this is non-zero, the score differences are correlated, and the
    joint distribution over 3+ candidates is multivariate normal with
    non-diagonal covariance — not reducible to independent binary
    comparisons. This is why NHG violates IIA for 3+ candidates
    ([flemming-2021] §9). -/
noncomputable def nhgCovariance (con : CON C n) (sigma : ℝ) (a b c : C) : ℝ :=
  sigma ^ 2 * ∑ i, ((con i b : ℝ) - (con i a : ℝ)) *
                   ((con i c : ℝ) - (con i a : ℝ))

/-- NHG covariance (ℚ, computable). -/
def nhgCovarianceQ (con : CON C n) (a b c : C) : ℚ :=
  ∑ i, ((con i b : ℚ) - (con i a : ℚ)) *
       ((con i c : ℚ) - (con i a : ℚ))

/-- The NHG self-covariance `Cov(ε_b − ε_a, ε_b − ε_a)` equals
    the variance `σ² · violationDiffSqSum`, recovering the binary case. -/
theorem nhgCovariance_self (con : CON C n) (sigma : ℝ) (a b : C) :
    nhgCovariance con sigma a b b =
    sigma ^ 2 * violationDiffSqSum con b a := by
  simp only [nhgCovariance, violationDiffSqSum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end HarmonicGrammar
