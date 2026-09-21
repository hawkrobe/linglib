import Linglib.Core.Probability.Choice.GumbelLuce
import Linglib.Core.Probability.Gaussian

/-!
# Signal detection theory

This file defines the equal-variance Gaussian model of signal detection theory, the account of
how an observer discriminates "signal present" from "noise only" when each hypothesis produces
a noisy internal response. The model follows the presentations of Green and Swets and of
Macmillan and Creelman, and its link to choice theory follows Luce and McFadden.

The parameterization is symmetric. The noise distribution is `N(-d'/2, 1)` and the
signal-plus-noise distribution is `N(d'/2, 1)`, so the sensitivity `d'` is the distance between
the two means, nonnegative by convention. The criterion `c` is measured from the midpoint
between the means, so `c = 0` is unbiased, and the observer responds "signal" when the internal
response exceeds `c`. With `tailProb m μ = P(X > c)` for `X` distributed as `N(μ, 1)`, which
equals `Φ(μ - c)` for the standard normal distribution function `Φ`, the hit rate is
`H = Φ(d'/2 - c)` and the false-alarm rate is `F = Φ(-d'/2 - c)`. The receiver operating
characteristic traces the pairs `(F, H)` as `c` varies at fixed `d'`, and lies above the
diagonal when `d' > 0`.

An observer is described by three quantities, two free and one derived. The sensitivity is
recovered from the rates as `z(H) - z(F)` and the criterion as `-(z(H) + z(F)) / 2`. The third,
`β = exp (d' * c)`, is the likelihood ratio at the criterion, and it is one for an unbiased
observer.

The likelihood ratio of signal to noise at an observation `x` is defined by its closed form
`L(x) = exp (d' * x)`, and the choice between reporting signal and noise follows a Luce model
whose odds are `L(x)`. `SDTModel.toLuceAt` builds that model as a binary Gumbel random-utility
model with utilities `(d' * x, 0)` and unit scale, so its signal probability
`L(x) / (L(x) + 1)` is the Bayesian posterior under a uniform prior
(`SDTModel.posteriorAt_uniform`). That posterior exceeds one half exactly when the observation
is positive (`SDTModel.posterior_gt_half_iff_pos_obs`), which is the sense in which the
criterion `c = 0` is optimal under a uniform prior.

## Main definitions

* `SDTModel`: the sensitivity and criterion of an observer.
* `SDTModel.hitRate`, `SDTModel.falseAlarmRate`: the two response rates.
* `dPrimeFromRates`, `biasFromRates`: the sensitivity and criterion recovered from the rates.
* `SDTModel.beta`: the likelihood ratio at the criterion.
* `rocCurve`: the hit rate as a function of the false-alarm rate at fixed sensitivity.
* `SDTModel.toLuceAt`: the Luce model of the report at an observation.
* `SDTModel.posteriorAt`: the posterior probability of signal at an observation.
* `logisticApproxConst`: the variance-matching constant `π/√3` of the logistic approximation.

## TODO

The likelihood ratio is defined as `exp (d' * x)`; that this is the ratio of the two Gaussian
densities is derived on paper and not proved here.

UNVERIFIED: that Luce's monograph gives the choice-theoretic framing of detection in its §2.E.

UNVERIFIED: that it gives the discriminal-process theory, of which detection theory is the
two-alternative case, in its §2.B-D.

UNVERIFIED: that the Bayes-optimal criterion under prior odds `π_N / π_S` is
`log (π_N / π_S) / d'`, a standard result attributed to Green and Swets and to Macmillan and
Creelman's first chapter. It is not formalized, since it needs Bayesian decision theory over a
continuous observation.

## References

* [R. D. Luce, *Individual Choice Behavior: A Theoretical Analysis* (1959)][luce-1959]
* [D. M. Green and J. A. Swets, *Signal Detection Theory and Psychophysics*
  (1966)][green-swets-1966]
* [N. A. Macmillan and C. D. Creelman, *Detection Theory: A User's Guide*
  (2005)][macmillan-creelman-2005]
* [D. McFadden, *Conditional logit analysis of qualitative choice behavior* (1974)][mcfadden-1974]
-/

namespace Core

open Real MeasureTheory BigOperators

section Model

/-! ## SDT model -/

/-- A signal detection model with equal-variance Gaussian distributions in the symmetric
parameterization. Neither field is constrained by the structure, and theorems that need `0 ≤ dPrime`
or `0 < dPrime` take it as a hypothesis, as mathlib's `gaussianReal μ v` leaves its parameters
unconstrained. -/
@[ext]
structure SDTModel where
  /-- The sensitivity is the signed distance between the signal-plus-noise mean and the noise mean
  in standard deviation units, nonnegative by convention. -/
  dPrime : ℝ
  /-- The criterion is the threshold for a "signal" response, measured from the midpoint between the
  two means, so that zero is unbiased, positive values favour "noise" and negative values favour
  "signal". -/
  criterion : ℝ

end Model

section TailProbabilities

/-! ## Hit and false-alarm rates as instances of `tailProb`

Both rates are tail probabilities of a unit-variance Gaussian shifted by ±d'/2:
hit rate is the tail at the *signal* mean, false-alarm rate is the tail at the
*noise* mean. Factoring the shared structure makes the bound proofs apply
uniformly. -/

/-- The tail probability `1 - Φ(c - μ)` is the probability that a response distributed as `N(μ, 1)`
exceeds the model's criterion `c`. -/
noncomputable def SDTModel.tailProb (m : SDTModel) (μ : ℝ) : ℝ :=
  1 - normalCDF (m.criterion - μ)

/-- The tail probability lies in `[0, 1]`. -/
@[simp]
theorem SDTModel.tailProb_mem_Icc (m : SDTModel) (μ : ℝ) :
    m.tailProb μ ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩ <;> simp only [SDTModel.tailProb]
  · linarith [normalCDF_le_one (m.criterion - μ)]
  · linarith [normalCDF_nonneg (m.criterion - μ)]

/-- The upper-tail probability is strictly monotone in the mean of the distribution, so shifting the
distribution rightward makes it larger. -/
theorem SDTModel.tailProb_strictMono (m : SDTModel) : StrictMono m.tailProb := by
  intro μ₁ μ₂ h
  simp only [SDTModel.tailProb]
  linarith [normalCDF_strictMono (show m.criterion - μ₂ < m.criterion - μ₁ by linarith)]

/-- The tail probability equals `Φ(μ - c)`. -/
@[simp]
theorem SDTModel.tailProb_eq_normalCDF (m : SDTModel) (μ : ℝ) :
    m.tailProb μ = normalCDF (μ - m.criterion) := by
  simp only [SDTModel.tailProb, show μ - m.criterion = -(m.criterion - μ) from by ring,
             normalCDF_neg]

/-- The hit rate is the probability of a "signal" response when the signal is present, the tail
probability at mean `d'/2`. -/
noncomputable def SDTModel.hitRate (m : SDTModel) : ℝ := m.tailProb (m.dPrime / 2)

/-- The false-alarm rate is the probability of a "signal" response to noise alone, the tail
probability at mean `-d'/2`. -/
noncomputable def SDTModel.falseAlarmRate (m : SDTModel) : ℝ := m.tailProb (-(m.dPrime / 2))

/-- The hit rate lies in `[0, 1]`. -/
@[simp]
theorem SDTModel.hitRate_mem_Icc (m : SDTModel) : m.hitRate ∈ Set.Icc (0 : ℝ) 1 :=
  m.tailProb_mem_Icc _

/-- The false-alarm rate lies in `[0, 1]`. -/
@[simp]
theorem SDTModel.falseAlarmRate_mem_Icc (m : SDTModel) :
    m.falseAlarmRate ∈ Set.Icc (0 : ℝ) 1 :=
  m.tailProb_mem_Icc _

/-- The hit rate is nonnegative. -/
theorem SDTModel.hitRate_nonneg (m : SDTModel) : 0 ≤ m.hitRate := m.hitRate_mem_Icc.1

/-- The hit rate is at most one. -/
theorem SDTModel.hitRate_le_one (m : SDTModel) : m.hitRate ≤ 1 := m.hitRate_mem_Icc.2

/-- The false-alarm rate is nonnegative. -/
theorem SDTModel.falseAlarmRate_nonneg (m : SDTModel) : 0 ≤ m.falseAlarmRate :=
  m.falseAlarmRate_mem_Icc.1

/-- The false-alarm rate is at most one. -/
theorem SDTModel.falseAlarmRate_le_one (m : SDTModel) : m.falseAlarmRate ≤ 1 :=
  m.falseAlarmRate_mem_Icc.2

/-- The proportion correct under equal presentation rates is `(H + (1 - F)) / 2`. -/
noncomputable def SDTModel.proportionCorrect (m : SDTModel) : ℝ :=
  (m.hitRate + (1 - m.falseAlarmRate)) / 2

end TailProbabilities

section Recovery

/-! ## Recovering `(d', c)` from observed rates

Standard SDT diagnostics come in pairs: from observed `(H, F)` an experimenter
recovers both the sensitivity `d' = z(H) - z(F)` and the response bias
`c = -(z(H) + z(F)) / 2`. Both are roundtrip-exact under the model. -/

variable (m : SDTModel)

/-- The sensitivity recovered from a hit rate and a false-alarm rate is `z(H) - z(F)`, where `z` is
the standard normal quantile function `probit`. -/
noncomputable def dPrimeFromRates (hitRate falseAlarmRate : ℝ) : ℝ :=
  probit hitRate - probit falseAlarmRate

/-- The criterion recovered from a hit rate and a false-alarm rate is `-(z(H) + z(F)) / 2`, where
`z` is the standard normal quantile function `probit`. -/
noncomputable def biasFromRates (hitRate falseAlarmRate : ℝ) : ℝ :=
  -(probit hitRate + probit falseAlarmRate) / 2

/-- Under the model the z-score of the hit rate is `d'/2 - c`. -/
private theorem probit_hitRate :
    probit m.hitRate = m.dPrime / 2 - m.criterion := by
  rw [SDTModel.hitRate, SDTModel.tailProb_eq_normalCDF, probit_normalCDF]

/-- Under the model the z-score of the false-alarm rate is `-d'/2 - c`. -/
private theorem probit_falseAlarmRate :
    probit m.falseAlarmRate = -(m.dPrime / 2) - m.criterion := by
  rw [SDTModel.falseAlarmRate, SDTModel.tailProb_eq_normalCDF, probit_normalCDF]

/-- The sensitivity recovered from the model's rates is the model's sensitivity. -/
@[simp]
theorem dPrimeFromRates_roundtrip :
    dPrimeFromRates m.hitRate m.falseAlarmRate = m.dPrime := by
  rw [dPrimeFromRates, probit_hitRate, probit_falseAlarmRate]; ring

/-- The criterion recovered from the model's rates is the model's criterion. -/
@[simp]
theorem biasFromRates_roundtrip :
    biasFromRates m.hitRate m.falseAlarmRate = m.criterion := by
  rw [biasFromRates, probit_hitRate, probit_falseAlarmRate]; ring

/-- For rates strictly between zero and one, the recovered sensitivity is positive exactly when the
hit rate exceeds the false-alarm rate. -/
theorem dPrimeFromRates_pos_iff {H F : ℝ}
    (hH_lo : 0 < H) (hH_hi : H < 1) (hF_lo : 0 < F) (hF_hi : F < 1) :
    0 < dPrimeFromRates H F ↔ F < H := by
  rw [dPrimeFromRates, sub_pos, probit_lt_iff hF_lo hF_hi hH_lo hH_hi]

end Recovery

section OperatingCharacteristic

/-! ## Operating characteristic `β` and unbiased observers -/

/-- The operating likelihood ratio `β = exp (d' * c)` is the model's likelihood ratio at its
criterion. -/
noncomputable def SDTModel.beta (m : SDTModel) : ℝ :=
  Real.exp (m.dPrime * m.criterion)

/-- The operating likelihood ratio is positive. -/
theorem SDTModel.beta_pos (m : SDTModel) : 0 < m.beta := exp_pos _

/-- An observer is unbiased when its criterion is zero. -/
def SDTModel.IsUnbiased (m : SDTModel) : Prop := m.criterion = 0

/-- The operating likelihood ratio of an unbiased observer is one. -/
theorem SDTModel.IsUnbiased.beta_eq_one {m : SDTModel} (h : m.IsUnbiased) :
    m.beta = 1 := by
  simp [SDTModel.beta, show m.criterion = 0 from h]

/-- With positive sensitivity an observer is unbiased exactly when its operating likelihood ratio is
one. -/
theorem SDTModel.isUnbiased_iff_beta_eq_one_of_pos
    (m : SDTModel) (hd : 0 < m.dPrime) :
    m.IsUnbiased ↔ m.beta = 1 := by
  refine ⟨SDTModel.IsUnbiased.beta_eq_one, fun h => ?_⟩
  have hlog : m.dPrime * m.criterion = 0 := by
    have := congrArg Real.log h
    rwa [SDTModel.beta, Real.log_exp, Real.log_one] at this
  rcases mul_eq_zero.mp hlog with hd0 | hc
  · exact absurd hd0 (ne_of_gt hd)
  · exact hc

/-- The hit rate and the false-alarm rate of an unbiased observer sum to one. -/
theorem SDTModel.IsUnbiased.hit_plus_fa_eq_one {m : SDTModel} (h : m.IsUnbiased) :
    m.hitRate + m.falseAlarmRate = 1 := by
  have hc : m.criterion = 0 := h
  simp only [SDTModel.hitRate, SDTModel.falseAlarmRate, SDTModel.tailProb,
    hc, zero_sub, zero_add, sub_neg_eq_add]
  have hneg : 1 - normalCDF (-(m.dPrime / 2)) = normalCDF (m.dPrime / 2) := by
    rw [normalCDF_neg]; ring
  rw [hneg]; ring

/-- The proportion correct of an unbiased observer of positive sensitivity exceeds one half. -/
theorem SDTModel.IsUnbiased.proportionCorrect_gt_half {m : SDTModel}
    (h : m.IsUnbiased) (hd : 0 < m.dPrime) :
    1/2 < m.proportionCorrect := by
  have hsum : m.hitRate + m.falseAlarmRate = 1 := h.hit_plus_fa_eq_one
  have hroc : m.falseAlarmRate < m.hitRate :=
    m.tailProb_strictMono (by linarith : -(m.dPrime / 2) < m.dPrime / 2)
  simp only [SDTModel.proportionCorrect]
  linarith

end OperatingCharacteristic

section ROC

/-! ## ROC curve -/

/-- The receiver operating characteristic at a sensitivity maps a false-alarm rate `F` to the hit
rate `1 - Φ(Φ⁻¹(1 - F) - d')` at the same criterion. -/
noncomputable def rocCurve (dPrime : ℝ) (falseAlarmRate : ℝ) : ℝ :=
  1 - normalCDF (probit (1 - falseAlarmRate) - dPrime)

/-- At zero sensitivity the receiver operating characteristic is the diagonal on the open unit
interval. -/
theorem roc_diagonal (f : ℝ) (hf : 0 < f) (hf' : f < 1) :
    rocCurve 0 f = f := by
  simp only [rocCurve, sub_zero]
  have h1f0 : 0 < 1 - f := by linarith
  have h1f1 : 1 - f < 1 := by linarith
  rw [probit_spec h1f0 h1f1]; ring

/-- At positive sensitivity the hit rate exceeds the false-alarm rate, so the receiver operating
characteristic lies above the diagonal. -/
theorem roc_above_diagonal (m : SDTModel) (hd : 0 < m.dPrime) :
    m.falseAlarmRate < m.hitRate :=
  m.tailProb_strictMono (by linarith : -(m.dPrime / 2) < m.dPrime / 2)

/-! The AUC integral identity
`∫₀¹ rocCurve d' f df = Φ(d'/√2)` (Green & Swets 1966 [green-swets-1966])
is correct but unproved — integrating `rocCurve` requires additional measure-
theoretic infrastructure not currently developed. -/

end ROC

section LuceEmbedding

/-! ## SDT as a Luce model — exact via McFadden's theorem

The SDT signal/noise choice is a binary Gumbel-Luce RUM: with utilities
`(d' · x, 0)` and unit Gumbel scale `β = 1`, the Gumbel max-probability reduces
to the SDT Luce policy exactly. The signal-probability and odds-ratio
properties below are immediate corollaries of `softmax_fin_two` and
`RationalAction.fromGumbelRUM_policy`. -/

/-- The likelihood ratio at an observation `x` is `exp (d' * x)`, the closed form of the ratio of
the density of `N(d'/2, 1)` to that of `N(-d'/2, 1)` at `x`. -/
noncomputable def likelihoodRatio (dPrime x : ℝ) : ℝ :=
  Real.exp (dPrime * x)

/-- The likelihood ratio is positive. -/
theorem likelihoodRatio_pos (dPrime x : ℝ) : 0 < likelihoodRatio dPrime x :=
  exp_pos _

/-- The likelihood ratio of a model at an observation is `likelihoodRatio` at the model's
sensitivity. -/
noncomputable def SDTModel.likelihoodRatioAt (m : SDTModel) (x : ℝ) : ℝ :=
  likelihoodRatio m.dPrime x

/-- The likelihood ratio of a model is positive. -/
theorem SDTModel.likelihoodRatioAt_pos (m : SDTModel) (x : ℝ) :
    0 < m.likelihoodRatioAt x := likelihoodRatio_pos _ _

/-- The report at an observation `x` is a binary Gumbel random-utility model with utilities `d' * x`
for signal and `0` for noise at unit scale, whose Luce scores are `exp (d' * x)` and `1`. The model
depends on the sensitivity and the observation and not on the criterion, which enters only in the
observer's response rule. -/
noncomputable def SDTModel.toLuceAt (m : SDTModel) (x : ℝ) :
    RationalAction Unit (Fin 2) :=
  RationalAction.fromGumbelRUM (fun i : Fin 2 => if i = 0 then m.dPrime * x else 0) 1

/-- The Luce score of reporting signal is the likelihood ratio. -/
@[simp]
theorem SDTModel.toLuceAt_score_signal (m : SDTModel) (x : ℝ) :
    (m.toLuceAt x).score () (0 : Fin 2) = m.likelihoodRatioAt x := by
  simp [SDTModel.toLuceAt, RationalAction.fromGumbelRUM, RationalAction.fromSoftmax,
        SDTModel.likelihoodRatioAt, likelihoodRatio]

/-- The Luce score of reporting noise is one. -/
@[simp]
theorem SDTModel.toLuceAt_score_noise (m : SDTModel) (x : ℝ) :
    (m.toLuceAt x).score () (1 : Fin 2) = 1 := by
  simp [SDTModel.toLuceAt, RationalAction.fromGumbelRUM, RationalAction.fromSoftmax]

/-- The Luce odds of signal to noise at an observation equal the likelihood ratio there. -/
theorem SDTModel.toLuceAt_odds_ratio (m : SDTModel) (x : ℝ) :
    (m.toLuceAt x).score () (0 : Fin 2) /
    (m.toLuceAt x).score () (1 : Fin 2) =
    m.likelihoodRatioAt x := by
  rw [m.toLuceAt_score_signal, m.toLuceAt_score_noise, div_one]

/-- The Luce probability of reporting signal at an observation is `L(x) / (L(x) + 1)` for the
likelihood ratio `L(x)`. -/
theorem SDTModel.toLuceAt_signal_prob (m : SDTModel) (x : ℝ) :
    (m.toLuceAt x).policy () (0 : Fin 2) =
    m.likelihoodRatioAt x / (m.likelihoodRatioAt x + 1) := by
  have h01 : ¬(1 : Fin 2) = (0 : Fin 2) := by decide
  rw [SDTModel.toLuceAt, RationalAction.fromGumbelRUM_policy, softmax_fin_two]
  simp only [Pi.smul_apply, smul_eq_mul, Fin.isValue, ↓reduceIte, h01, inv_one, one_mul,
             mul_zero, sub_zero, Real.sigmoid_def, SDTModel.likelihoodRatioAt,
             likelihoodRatio]
  rw [Real.exp_neg]
  have h := (Real.exp_pos (m.dPrime * x)).ne'
  field_simp

end LuceEmbedding

section BayesianInterpretation

/-! ## Bayesian posterior interpretation

The SDT Luce policy is exactly the Bayesian posterior on "signal present"
under uniform prior odds. Under non-uniform prior `π_S` for signal, the
posterior is `π_S · L(x) / (π_S · L(x) + (1 - π_S))` — the same formula but
with prior-weighted likelihoods. With `π_S = 1/2`, this reduces to
`L(x) / (L(x) + 1) = (m.toLuceAt x).policy () 0`.

### Why `posteriorAt` is a closed form

The SDT observer's hypothesis space is binary (`{signal, noise} = Fin 2`)
and finite, but the *observation* `x : ℝ` is *continuous* (a real-valued
internal response). The discrete Bayes lemmas of
`Core/Probability/Kernel/Posterior.lean` evaluate a kernel posterior at
observations of positive mass, which a continuous observation never has.
The right mathlib substrate for the continuous binary case is a posterior
kernel against a density, which is not set up here, so
`SDTModel.posteriorAt` states the closed-form Bayes' rule directly. -/

variable (m : SDTModel)

/-- The posterior probability of signal at an observation `x` under a prior probability
`priorSignal` of signal is `π * L(x) / (π * L(x) + (1 - π))`, Bayes' rule for the two hypotheses at
likelihood ratio `L(x)`. -/
noncomputable def SDTModel.posteriorAt (x : ℝ) (priorSignal : ℝ) : ℝ :=
  priorSignal * m.likelihoodRatioAt x /
    (priorSignal * m.likelihoodRatioAt x + (1 - priorSignal))

/-- For a positive likelihood ratio `L` the posterior under a uniform prior is `L / (L + 1)`. -/
private lemma posterior_uniform_eq_div {L : ℝ} (hL : 0 < L) :
    (1 : ℝ) / 2 * L / ((1 : ℝ) / 2 * L + (1 - 1 / 2)) = L / (L + 1) := by
  have hLp1 : (0 : ℝ) < L + 1 := by linarith
  have hLp1_ne : L + 1 ≠ 0 := ne_of_gt hLp1
  field_simp; ring

/-- For positive `L` the quantity `L / (L + 1)` exceeds one half exactly when `L` exceeds one. -/
private lemma half_lt_div_add_one_iff {L : ℝ} (hL : 0 < L) :
    1 / 2 < L / (L + 1) ↔ 1 < L := by
  have hLp1 : (0 : ℝ) < L + 1 := by linarith
  rw [lt_div_iff₀ hLp1]; constructor <;> intro h <;> linarith

/-- Under a uniform prior the posterior probability of signal at an observation is the Luce
probability of reporting signal there. -/
theorem SDTModel.posteriorAt_uniform (x : ℝ) :
    m.posteriorAt x (1/2) = (m.toLuceAt x).policy () (0 : Fin 2) := by
  rw [m.toLuceAt_signal_prob, SDTModel.posteriorAt]
  exact posterior_uniform_eq_div (m.likelihoodRatioAt_pos x)

/-- With positive sensitivity and a uniform prior the posterior probability of signal exceeds one
half exactly when the observation is positive. -/
theorem SDTModel.posterior_gt_half_iff_pos_obs (x : ℝ) (hd : 0 < m.dPrime) :
    1/2 < m.posteriorAt x (1/2) ↔ 0 < x := by
  rw [SDTModel.posteriorAt, posterior_uniform_eq_div (m.likelihoodRatioAt_pos x),
      half_lt_div_add_one_iff (m.likelihoodRatioAt_pos x),
      SDTModel.likelihoodRatioAt, likelihoodRatio,
      show (1 : ℝ) = Real.exp 0 from exp_zero.symm, Real.exp_lt_exp]
  exact ⟨fun h => (mul_pos_iff_of_pos_left hd).mp h, fun h => mul_pos hd h⟩

end BayesianInterpretation

section LogisticApproximation

/-! ## Logistic approximation constant

The SDT hit rate `Φ(d'/2 - c)` is well-approximated by `logistic(k · (d'/2 - c))`
where `k = π/√3 ≈ 1.814` is the variance-matching constant:

  `Φ(x) ≈ logistic(x · π/√3)` with max error `≈ 0.023`.

This is the Thurstone-Luce bridge for the detection context: both SDT
(Gaussian noise) and the Gumbel-Luce model (Gumbel noise) are Random
Utility Models. The Gumbel-Luce model gives **exactly** logistic
probabilities (Lemma 1 of [mcfadden-1974]; see `integral_gumbelPDFReal_mul_prod_cdf`
in `Core/Probability/Gumbel.lean`). The Gaussian model gives `Φ`. These agree up to the
numerical approximation `Φ ≈ logistic`.

The variance-matching constant `π/√3 ≈ 1.8138` is exact (logistic has
variance `π²/3`, so scaling `Φ` by `π/√3` matches unit-variance normal).
The optimal sup-norm constant for `Φ(x) ≈ σ(k · x)` is approximately
`1.7009` (Page 1977). We use `π/√3` rather than the sup-norm optimum
because it has a clean variance-matching derivation. UNVERIFIED: the sup-error figure `≈ 0.023` is
quoted from secondary sources; verify against Bowling et al. 2009 or
Page 1977 before relying on it. -/

/-- The logistic approximation constant `π/√3` is the scale that matches the variance `π²/3` of the
standard logistic distribution to the unit variance of the standard normal. -/
noncomputable def logisticApproxConst : ℝ := Real.pi / Real.sqrt 3

/-- The logistic approximation constant is positive. -/
theorem logisticApproxConst_pos : 0 < logisticApproxConst :=
  div_pos Real.pi_pos (Real.sqrt_pos.mpr (by norm_num))

end LogisticApproximation

end Core
