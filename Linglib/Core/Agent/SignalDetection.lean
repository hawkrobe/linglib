import Linglib.Core.Agent.RationalAction
import Linglib.Core.Agent.NormalCDF

/-!
# Signal Detectability Theory (@cite{luce-1959}, §2.E) @cite{luce-1959}
@cite{green-swets-1966} @cite{macmillan-creelman-2005}

Signal Detection Theory (SDT) models the observer's task of discriminating
between two hypotheses — "signal present" (sN) and "noise only" (N) — when
each hypothesis generates a noisy internal response. Under the equal-variance
Gaussian model, the noise distribution has mean 0 and the signal+noise
distribution has mean d' (the **sensitivity** or **detectability** parameter),
both with unit variance.

The observer's decision rule is to respond "signal" when the internal response
exceeds a **criterion** c. This yields two key probabilities:

- **Hit rate**: H = P("signal" | sN) = 1 - Phi(c - d'/2)
- **False alarm rate**: F = P("signal" | N) = 1 - Phi(c + d'/2)

where Phi is the standard normal CDF.

The **ROC curve** (Receiver Operating Characteristic) traces out the (F, H)
pairs as c varies, for a fixed d'. When d' > 0, the curve lies above the
diagonal (H > F), reflecting genuine discriminability.

## Connection to Luce's Choice Framework

Luce (§2.E) shows that SDT can be embedded in his choice-theoretic framework.
The likelihood ratio at observation x is:

  L(x) = f_{sN}(x) / f_N(x) = exp(d' * x - d'^2/2)

This is a ratio scale value, and the observer's "choice" between reporting
signal vs noise follows a Luce model with v(signal)/v(noise) = L(x).

## Connection to Thurstone

SDT is essentially Thurstone's discriminal process theory (§2.B-D) applied
to the two-alternative detection context. The d' parameter is the standardized
distance between the two discriminal dispersions, and the logistic approximation
to the Gaussian CDF connects SDT choice probabilities to the Luce-Thurstone
logistic choice model.

-/

set_option autoImplicit false

namespace Core

open Real MeasureTheory BigOperators

-- ============================================================================
-- §2. SDT Model
-- ============================================================================

/-- A Signal Detection Theory model with equal-variance Gaussian assumptions.

    - `d_prime`: sensitivity (d'), the standardized distance between the
      signal+noise and noise-only distribution means. Non-negative by
      convention (d' = 0 means no discriminability).
    - `criterion`: the observer's response criterion c. The observer
      responds "signal" when the internal response exceeds c.
      c = 0 is unbiased; c > 0 is conservative (favors "noise");
      c < 0 is liberal (favors "signal"). -/
structure SDTModel where
  /-- Sensitivity: distance between signal+noise and noise means (in SD units). -/
  d_prime : ℝ
  /-- Response criterion: threshold for "signal" response. -/
  criterion : ℝ
  /-- Sensitivity is non-negative. -/
  d_prime_nonneg : 0 ≤ d_prime

/-- Hit rate: P("signal" | signal present) = 1 - Phi(c - d'/2).

    Under the equal-variance Gaussian model, the signal+noise distribution
    has mean d' and variance 1. The observer responds "signal" when the
    internal response exceeds c. After standardizing:
    H = P(X > c | sN) = P(Z > c - d') = 1 - Phi(c - d')

    In the symmetric parameterization (means at +d'/2 and -d'/2):
    H = 1 - Phi(c - d'/2). -/
noncomputable def SDTModel.hitRate (m : SDTModel) : ℝ :=
  1 - normalCDF (m.criterion - m.d_prime / 2)

/-- False alarm rate: P("signal" | noise only) = 1 - Phi(c + d'/2).

    Under the equal-variance Gaussian model, the noise distribution has
    mean 0 and variance 1. The observer responds "signal" when the
    internal response exceeds c. After standardizing:
    F = P(X > c | N) = P(Z > c) = 1 - Phi(c)

    In the symmetric parameterization (means at +d'/2 and -d'/2):
    F = 1 - Phi(c + d'/2). -/
noncomputable def SDTModel.falseAlarmRate (m : SDTModel) : ℝ :=
  1 - normalCDF (m.criterion + m.d_prime / 2)

/-- Hit rate is between 0 and 1. -/
theorem SDTModel.hitRate_nonneg (m : SDTModel) : 0 ≤ m.hitRate := by
  simp only [hitRate]
  linarith [normalCDF_le_one (m.criterion - m.d_prime / 2)]

theorem SDTModel.hitRate_le_one (m : SDTModel) : m.hitRate ≤ 1 := by
  simp only [hitRate]
  linarith [normalCDF_nonneg (m.criterion - m.d_prime / 2)]

/-- False alarm rate is between 0 and 1. -/
theorem SDTModel.falseAlarmRate_nonneg (m : SDTModel) : 0 ≤ m.falseAlarmRate := by
  simp only [falseAlarmRate]
  linarith [normalCDF_le_one (m.criterion + m.d_prime / 2)]

theorem SDTModel.falseAlarmRate_le_one (m : SDTModel) : m.falseAlarmRate ≤ 1 := by
  simp only [falseAlarmRate]
  linarith [normalCDF_nonneg (m.criterion + m.d_prime / 2)]

-- ============================================================================
-- §3. Recovering d' from Observed Rates
-- ============================================================================

/-- The probit function (inverse normal CDF): for `p ∈ (0, 1)`, returns
    the unique `x` with `Φ(x) = p`. Returns 0 for out-of-range inputs.

    Existence follows from the Intermediate Value Theorem applied to the
    continuous, strictly monotone `normalCDF` with limits 0 at -∞ and 1 at +∞. -/
noncomputable def probit (p : ℝ) : ℝ :=
  if h : 0 < p ∧ p < 1 then
    Classical.choose (normalCDF_surj_Ioo p h.1 h.2)
  else 0

/-- Specification: `Φ(probit(p)) = p` for `p ∈ (0, 1)`. -/
theorem probit_spec {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    normalCDF (probit p) = p := by
  simp only [probit, hp0, hp1, and_self, dite_true]
  exact Classical.choose_spec (normalCDF_surj_Ioo p hp0 hp1)

/-- Specification: `probit(Φ(x)) = x` for all `x` (left inverse). -/
theorem probit_normalCDF (x : ℝ) : probit (normalCDF x) = x := by
  have hp0 : 0 < normalCDF x :=
    lt_of_le_of_lt (normalCDF_nonneg (x - 1)) (normalCDF_strictMono (by linarith))
  have hp1 : normalCDF x < 1 :=
    lt_of_lt_of_le (normalCDF_strictMono (by linarith : x < x + 1)) (normalCDF_le_one (x + 1))
  exact normalCDF_injective (probit_spec hp0 hp1)

/-- Recover d' from hit and false alarm rates.
    d' = Phi^{-1}(1 - F) - Phi^{-1}(1 - H) = z(H) - z(F)
    where z = probit (the quantile function of the standard normal). -/
noncomputable def dPrimeFromRates (hitRate falseAlarmRate : ℝ) : ℝ :=
  probit hitRate - probit falseAlarmRate

/-- Roundtrip: recovering d' from the hit and false alarm rates of an SDT model
    returns the original d'. -/
theorem dPrimeFromRates_roundtrip (m : SDTModel) :
    dPrimeFromRates m.hitRate m.falseAlarmRate = m.d_prime := by
  simp only [dPrimeFromRates, SDTModel.hitRate, SDTModel.falseAlarmRate] at *
  -- probit(1 - Φ(c - d'/2)) - probit(1 - Φ(c + d'/2))
  -- = probit(Φ(d'/2 - c)) - probit(Φ(-d'/2 - c))     by normalCDF_neg
  -- = (d'/2 - c) - (-d'/2 - c)                         by probit_normalCDF
  -- = d'
  conv_lhs =>
    rw [show 1 - normalCDF (m.criterion - m.d_prime / 2) =
          normalCDF (-(m.criterion - m.d_prime / 2)) from by rw [normalCDF_neg],
        show 1 - normalCDF (m.criterion + m.d_prime / 2) =
          normalCDF (-(m.criterion + m.d_prime / 2)) from by rw [normalCDF_neg]]
  rw [probit_normalCDF, probit_normalCDF]; ring

-- ============================================================================
-- §4. ROC Curve
-- ============================================================================

/-- The ROC curve for a given d': maps false alarm rate to hit rate as the
    criterion varies. Parameterized by criterion c:

    (F(c), H(c)) = (1 - Phi(c + d'/2), 1 - Phi(c - d'/2))

    Eliminating c: H = Phi(Phi^{-1}(F) + d'), or equivalently
    H = 1 - Phi(Phi^{-1}(1-F) - d').

    We define the ROC curve directly as a function of the false alarm rate. -/
noncomputable def rocCurve (d_prime : ℝ) (falseAlarmRate : ℝ) : ℝ :=
  1 - normalCDF (probit (1 - falseAlarmRate) - d_prime)

/-- For d' = 0, the ROC curve is the diagonal: H = F (chance performance). -/
theorem roc_diagonal (f : ℝ) (hf : 0 < f) (hf' : f < 1) :
    rocCurve 0 f = f := by
  simp only [rocCurve, sub_zero]
  have h1f0 : 0 < 1 - f := by linarith
  have h1f1 : 1 - f < 1 := by linarith
  rw [probit_spec h1f0 h1f1]; ring

/-- For d' > 0, the ROC curve lies above the diagonal: H > F.

    This is the fundamental result of SDT — positive sensitivity means the
    observer performs above chance. Intuitively, when d' > 0, the signal+noise
    distribution is shifted right of the noise distribution, so for any
    criterion, more of the signal distribution exceeds the criterion than
    the noise distribution.

    Proof: H - F = [1 - Phi(c - d'/2)] - [1 - Phi(c + d'/2)]
                 = Phi(c + d'/2) - Phi(c - d'/2) > 0
    since Phi is strictly increasing and d' > 0 implies c + d'/2 > c - d'/2. -/
theorem roc_above_diagonal (m : SDTModel) (hd : 0 < m.d_prime) :
    m.falseAlarmRate < m.hitRate := by
  simp only [SDTModel.hitRate, SDTModel.falseAlarmRate]
  have h : m.criterion - m.d_prime / 2 < m.criterion + m.d_prime / 2 := by linarith
  linarith [normalCDF_strictMono h]

/-- Higher d' implies higher area under the ROC curve.

    The area under the ROC curve (AUC) equals Phi(d'/sqrt(2)) for the
    equal-variance Gaussian model. Since Phi is increasing, higher d'
    yields higher AUC. -/
theorem roc_area_increases_with_dprime (d₁ d₂ : ℝ) (h : d₁ < d₂) :
    normalCDF (d₁ / Real.sqrt 2) < normalCDF (d₂ / Real.sqrt 2) := by
  exact normalCDF_strictMono (div_lt_div_of_pos_right h (Real.sqrt_pos.mpr (by norm_num)))

-- ============================================================================
-- §5. SDT as a Luce Model
-- ============================================================================

/-- The Gaussian likelihood ratio at observation x, given d':

    L(x) = f_{sN}(x) / f_N(x) = exp(d' * x - d'^2 / 2)

    where f_N ~ N(0,1) and f_{sN} ~ N(d', 1). This follows from:
    log L(x) = log f_{sN}(x) - log f_N(x)
             = [-(x-d')^2/2] - [-x^2/2]
             = d'*x - d'^2/2. -/
noncomputable def likelihoodRatio (d_prime x : ℝ) : ℝ :=
  Real.exp (d_prime * x - d_prime ^ 2 / 2)

/-- The likelihood ratio is always positive (being an exponential). -/
theorem likelihoodRatio_pos (d_prime x : ℝ) : 0 < likelihoodRatio d_prime x :=
  exp_pos _

/-- SDT embedded as a Luce choice model: the "choice" between reporting
    signal vs noise, given observation x, has score ratio equal to the
    likelihood ratio.

    In Luce's framework (Chapter 1), the response ratio is:
    P("signal" | x) / P("noise" | x) = v(signal) / v(noise) = L(x)

    We construct a RationalAction on Fin 2 (signal = 0, noise = 1) with
    scores proportional to the likelihood ratio. -/
noncomputable def sdt_as_luce (d_prime x : ℝ) : RationalAction Unit (Fin 2) where
  score _ a := if a = 0 then likelihoodRatio d_prime x else 1
  score_nonneg _ a := by
    split
    · exact le_of_lt (likelihoodRatio_pos d_prime x)
    · exact le_of_lt one_pos

/-- The policy of the Luce-SDT model for "signal" (action 0) is the
    likelihood ratio divided by (1 + likelihood ratio), i.e., the
    logistic transform of the log-likelihood ratio. -/
theorem sdt_luce_signal_prob (d_prime x : ℝ) :
    (sdt_as_luce d_prime x).policy () (0 : Fin 2) =
    likelihoodRatio d_prime x / (likelihoodRatio d_prime x + 1) := by
  simp only [RationalAction.policy, RationalAction.totalScore, sdt_as_luce,
    Fin.sum_univ_two, Fin.isValue]
  have h01 : ¬(1 : Fin 2) = (0 : Fin 2) := by decide
  simp only [↓reduceIte, h01]
  have hpos : 0 < likelihoodRatio d_prime x + 1 := by
    linarith [likelihoodRatio_pos d_prime x]
  simp only [ne_of_gt hpos, ↓reduceIte]

/-- The odds ratio of the SDT Luce model equals the likelihood ratio.

    This is the core connection: Luce's choice-theoretic ratio scale
    v(signal)/v(noise) IS the likelihood ratio from SDT. -/
theorem sdt_luce_odds_ratio (d_prime x : ℝ) :
    (sdt_as_luce d_prime x).score () (0 : Fin 2) /
    (sdt_as_luce d_prime x).score () (1 : Fin 2) =
    likelihoodRatio d_prime x := by
  simp only [sdt_as_luce, Fin.isValue]
  have h01 : ¬(1 : Fin 2) = (0 : Fin 2) := by decide
  simp only [↓reduceIte, h01]
  rw [div_one]

-- ============================================================================
-- §6. Variance-Matching Constant
-- ============================================================================

/-!
## Logistic Approximation Constant

The SDT hit rate `Φ(d'/2 - c)` is well-approximated by `logistic(k·(d'/2-c))`
where `k = π/√3 ≈ 1.814` is the variance-matching constant:

    `Φ(x) ≈ logistic(x · π/√3)` with max error ~0.023

This is the Thurstone-Luce bridge for the detection context: both SDT
(Gaussian noise) and the Gumbel-Luce model (Gumbel noise) are Random
Utility Models. The Gumbel-Luce model gives **exactly** logistic
probabilities (McFadden's theorem, `GumbelLuce.lean`). The Gaussian
model gives Φ. These agree up to the numerical approximation `Φ ≈ logistic`.

The constant `k = π/√3` equals `thurstoneLuceK(1/√2)`, unifying the SDT
and Thurstone parameterizations (see `logisticApproxConst_eq_thurstoneLuceK`
in `GaussianChoice.lean`).
-/

/-- The logistic approximation constant: k = π/√3 ≈ 1.814.

    This is the variance-matching scale factor between the normal and
    logistic distributions: the standard logistic has variance π²/3,
    so `Φ(x) ≈ logistic(x · π/√3)` with max error ~0.023.

    Note: the optimal constant minimizing the sup-norm is ~1.702
    (slightly smaller than π/√3). We use π/√3 because it has a clean
    analytical derivation from variance matching and equals
    `thurstoneLuceK(1/√2)` (see `logisticApproxConst_eq_thurstoneLuceK`). -/
noncomputable def logisticApproxConst : ℝ := Real.pi / Real.sqrt 3

end Core
