import Linglib.Core.Agent.GumbelLuce
import Linglib.Core.Probability.Gaussian

/-!
# Signal Detection Theory @cite{luce-1959} @cite{green-swets-1966} @cite{macmillan-creelman-2005}

Signal Detection Theory (SDT) models the observer's task of discriminating
between two hypotheses — "signal present" (sN) and "noise only" (N) — when
each hypothesis generates a noisy internal response.

## Symmetric parameterization

We adopt the *symmetric* equal-variance Gaussian model throughout: the noise
distribution is `N(-d'/2, 1)` and the signal+noise distribution is `N(d'/2, 1)`,
both with unit variance. The criterion `c` is measured from the midpoint
between the two distributions (so `c = 0` is unbiased). The single parameter
`d'` (the **sensitivity** or **detectability** index) is the signed distance
between the two means and is `≥ 0` by convention.

The observer responds "signal" when the internal response exceeds `c`. Writing
`tailProb m μ := P(X > c | X ~ N(μ, 1)) = 1 - Φ(c - μ) = Φ(μ - c)`, both rates
are instances:

- **Hit rate**: `H = tailProb m (d'/2) = Φ(d'/2 - c)`
- **False alarm rate**: `F = tailProb m (-d'/2) = Φ(-d'/2 - c)`

where `Φ` is the standard normal CDF.

The **ROC curve** (Receiver Operating Characteristic) traces out the `(F, H)`
pairs as `c` varies, for a fixed `d'`. When `d' > 0`, the curve lies above the
diagonal (`H > F`), reflecting genuine discriminability.

## Standard observer characterization: (d', c, β)

An equal-variance Gaussian SDT observer is characterized by three quantities,
two free and one derived:

- `dPrime` (`d'`) — sensitivity, recoverable from rates as `z(H) - z(F)`.
- `criterion` (`c`) — response bias, recoverable from rates as `-(z(H) + z(F))/2`.
- `beta` (`β`) — likelihood ratio at the criterion: `β = exp(d' · c)`.

Under uniform prior odds and 0–1 loss, the Bayes-optimal criterion is `c = 0`
(`β = 1`); under prior odds `π_N / π_S` it is `c* = log(π_N / π_S) / d'`.

## Connection to Luce's choice framework (McFadden's theorem, exact)

Under the symmetric parameterization, the likelihood ratio at observation `x`
(measured from the midpoint between the two distribution means) is

  `L(x) = f_{sN}(x) / f_N(x) = exp(d' · x)`

and the observer's "choice" between reporting signal vs noise follows a Luce
model with `v(signal) / v(noise) = L(x)`. We construct this Luce model as
`SDTModel.toLuceAt`, defined directly as a `RationalAction.fromGumbelRUM` with
binary utilities `(d' · x, 0)` and scale `β = 1`. The signal probability and
odds-ratio properties are then immediate corollaries of `mcfaddenIntegral_binary`
and `RationalAction.fromGumbelRUM_policy` — making the SDT/Gumbel-Luce
equivalence formally exact for binary detection (UNVERIFIED: @cite{luce-1959}
§2.E gives this as the original choice-theoretic framing).

## Connection to Thurstone

SDT is essentially Thurstone's discriminal-process theory (UNVERIFIED:
@cite{luce-1959} §2.B–D) applied to the two-alternative detection context.
The formal identity `SDTModel.hitRate = ThurstoneCaseV.choiceProb` under the
yes/no Thurstone model with `σ = 1/√2` is proved as
`SDTModel.hitRate_eq_thurstone` in `GaussianChoice.lean`. The 2AFC version is
`SDTModel.twoAFC_eq_thurstone` in the same file. The logistic approximation
`Φ ≈ logistic` connects SDT choice probabilities to the Luce-Thurstone
logistic choice model — see `GumbelLuce.lean` and
`logisticApproxConst_eq_thurstoneLuceK` in `GaussianChoice.lean`.

## References

- @cite{luce-1959} — original choice-theoretic framing.
- @cite{green-swets-1966} — canonical SDT reference.
- @cite{macmillan-creelman-2005} — modern textbook treatment of `d'`,
  `z(H) - z(F)`, `c = -(z(H) + z(F))/2`, AUC = `Φ(d'/√2)`, and the
  equal-variance Gaussian model.
- @cite{mcfadden-1974} — Gumbel-Luce equivalence, used here for the SDT/Luce
  binary identity.
-/

namespace Core

open Real MeasureTheory BigOperators

section Model

/-! ## SDT model -/

/-- A Signal Detection Theory model with equal-variance Gaussian assumptions
    in the *symmetric* parameterization.

    - `dPrime`: sensitivity (`d'`), the standardized distance between the
      signal+noise mean (`+d'/2`) and the noise mean (`-d'/2`). Non-negative
      by convention; `d' = 0` means no discriminability. (Not enforced as a
      structure invariant — theorems that need `0 ≤ d'` or `0 < d'` take it
      as an explicit hypothesis. This matches mathlib's `gaussianReal μ v`
      discipline of leaving inert parameters unconstrained at the type level.)
    - `criterion`: the observer's response criterion `c`, measured from the
      midpoint between the two distribution means. The observer responds
      "signal" when the internal response exceeds `c`. `c = 0` is unbiased;
      `c > 0` is conservative (favors "noise"); `c < 0` is liberal (favors
      "signal"). -/
@[ext]
structure SDTModel where
  /-- Sensitivity: signed distance between signal+noise and noise means
      (in standard deviation units). Non-negative by convention but not
      enforced — pass `(h : 0 ≤ m.dPrime)` to theorems that need it. -/
  dPrime : ℝ
  /-- Response criterion: threshold for "signal" response, measured from the
      midpoint between the signal+noise and noise means. -/
  criterion : ℝ

end Model

section TailProbabilities

/-! ## Hit and false-alarm rates as instances of `tailProb`

Both rates are tail probabilities of a unit-variance Gaussian shifted by ±d'/2:
hit rate is the tail at the *signal* mean, false-alarm rate is the tail at the
*noise* mean. Factoring the shared structure makes the bound proofs apply
uniformly. -/

/-- Tail probability of `N(μ, 1)` at the model's criterion `c`:

    `tailProb m μ = P(X > c | X ~ N(μ, 1)) = 1 - Φ(c - μ) = Φ(μ - c)`.

    Both `hitRate` (with `μ = d'/2`) and `falseAlarmRate` (with `μ = -d'/2`)
    are instances. -/
noncomputable def SDTModel.tailProb (m : SDTModel) (μ : ℝ) : ℝ :=
  1 - normalCDF (m.criterion - μ)

/-- The tail probability lies in `[0, 1]`. -/
@[simp]
theorem SDTModel.tailProb_mem_Icc (m : SDTModel) (μ : ℝ) :
    m.tailProb μ ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩ <;> simp only [SDTModel.tailProb]
  · linarith [normalCDF_le_one (m.criterion - μ)]
  · linarith [normalCDF_nonneg (m.criterion - μ)]

/-- `tailProb` is strictly monotone in the distribution mean: shifting the
    distribution rightward (larger μ) makes the upper-tail probability larger.

    This is the engine behind `roc_above_diagonal`: the signal+noise mean
    `+d'/2` exceeds the noise mean `-d'/2` whenever `d' > 0`, so the hit rate
    exceeds the false-alarm rate. -/
theorem SDTModel.tailProb_strictMono (m : SDTModel) : StrictMono m.tailProb := by
  intro μ₁ μ₂ h
  simp only [SDTModel.tailProb]
  linarith [normalCDF_strictMono (show m.criterion - μ₂ < m.criterion - μ₁ by linarith)]

/-- Symmetric form via `Φ(μ - c)`, often more convenient than the `1 - Φ` form. -/
@[simp]
theorem SDTModel.tailProb_eq_normalCDF (m : SDTModel) (μ : ℝ) :
    m.tailProb μ = normalCDF (μ - m.criterion) := by
  simp only [SDTModel.tailProb, show μ - m.criterion = -(m.criterion - μ) from by ring,
             normalCDF_neg]

/-- Hit rate `H = P("signal" | signal present)` = tail at `μ = d'/2`. -/
noncomputable def SDTModel.hitRate (m : SDTModel) : ℝ := m.tailProb (m.dPrime / 2)

/-- False alarm rate `F = P("signal" | noise only)` = tail at `μ = -d'/2`. -/
noncomputable def SDTModel.falseAlarmRate (m : SDTModel) : ℝ := m.tailProb (-(m.dPrime / 2))

/-- Both rates lie in `[0, 1]`. -/
@[simp]
theorem SDTModel.hitRate_mem_Icc (m : SDTModel) : m.hitRate ∈ Set.Icc (0 : ℝ) 1 :=
  m.tailProb_mem_Icc _

@[simp]
theorem SDTModel.falseAlarmRate_mem_Icc (m : SDTModel) :
    m.falseAlarmRate ∈ Set.Icc (0 : ℝ) 1 :=
  m.tailProb_mem_Icc _

/-- Hit rate is non-negative (corollary of `hitRate_mem_Icc`). -/
theorem SDTModel.hitRate_nonneg (m : SDTModel) : 0 ≤ m.hitRate := m.hitRate_mem_Icc.1

/-- Hit rate is at most 1. -/
theorem SDTModel.hitRate_le_one (m : SDTModel) : m.hitRate ≤ 1 := m.hitRate_mem_Icc.2

/-- False alarm rate is non-negative. -/
theorem SDTModel.falseAlarmRate_nonneg (m : SDTModel) : 0 ≤ m.falseAlarmRate :=
  m.falseAlarmRate_mem_Icc.1

/-- False alarm rate is at most 1. -/
theorem SDTModel.falseAlarmRate_le_one (m : SDTModel) : m.falseAlarmRate ≤ 1 :=
  m.falseAlarmRate_mem_Icc.2

/-- **Proportion correct** assuming equal presentation rates: the standard
    summary accuracy statistic, `(H + (1 - F)) / 2`. With unbiased criterion
    and `d' > 0`, this strictly exceeds `1/2`. -/
noncomputable def SDTModel.proportionCorrect (m : SDTModel) : ℝ :=
  (m.hitRate + (1 - m.falseAlarmRate)) / 2

end TailProbabilities

section Recovery

/-! ## Recovering `(d', c)` from observed rates

Standard SDT diagnostics come in pairs: from observed `(H, F)` an experimenter
recovers both the sensitivity `d' = z(H) - z(F)` and the response bias
`c = -(z(H) + z(F)) / 2`. Both are roundtrip-exact under the model. -/

variable (m : SDTModel)

/-- Recover `d'` from hit and false alarm rates:
    `d' = z(H) - z(F) = Φ⁻¹(H) - Φ⁻¹(F)`

    where `z = probit` is the standard-normal quantile function. Under the
    symmetric parameterization, `z(H) = d'/2 - c` and `z(F) = -d'/2 - c`,
    so the difference is `d'` regardless of `c`. -/
noncomputable def dPrimeFromRates (hitRate falseAlarmRate : ℝ) : ℝ :=
  probit hitRate - probit falseAlarmRate

/-- Recover the response bias `c` from hit and false alarm rates:
    `c = -(z(H) + z(F)) / 2`.

    Under the symmetric parameterization, `z(H) + z(F) = -2c`, so the
    negated half is `c` regardless of `d'`. This is the standard SDT bias
    diagnostic; together with `dPrimeFromRates`, the two functions invert
    the model from observed rates. -/
noncomputable def biasFromRates (hitRate falseAlarmRate : ℝ) : ℝ :=
  -(probit hitRate + probit falseAlarmRate) / 2

/-- Helper: under the model, `z(H) = d'/2 - c`. -/
private theorem probit_hitRate :
    probit m.hitRate = m.dPrime / 2 - m.criterion := by
  rw [SDTModel.hitRate, SDTModel.tailProb_eq_normalCDF, probit_normalCDF]

/-- Helper: under the model, `z(F) = -d'/2 - c`. -/
private theorem probit_falseAlarmRate :
    probit m.falseAlarmRate = -(m.dPrime / 2) - m.criterion := by
  rw [SDTModel.falseAlarmRate, SDTModel.tailProb_eq_normalCDF, probit_normalCDF]

/-- Roundtrip: `d'` recovered from rates equals the model's `d'`. -/
@[simp]
theorem dPrimeFromRates_roundtrip :
    dPrimeFromRates m.hitRate m.falseAlarmRate = m.dPrime := by
  rw [dPrimeFromRates, probit_hitRate, probit_falseAlarmRate]; ring

/-- Roundtrip: `c` recovered from rates equals the model's criterion. -/
@[simp]
theorem biasFromRates_roundtrip :
    biasFromRates m.hitRate m.falseAlarmRate = m.criterion := by
  rw [biasFromRates, probit_hitRate, probit_falseAlarmRate]; ring

/-- `d'` recovered from hit rate `H` and false alarm rate `F` is positive
    iff `H > F`. This is the fundamental connection between SDT sensitivity
    and observable discrimination: an observer with `d' > 0` can tell signal
    from noise above chance. -/
theorem dPrimeFromRates_pos_iff {H F : ℝ}
    (hH_lo : 0 < H) (hH_hi : H < 1) (hF_lo : 0 < F) (hF_hi : F < 1) :
    0 < dPrimeFromRates H F ↔ F < H := by
  rw [dPrimeFromRates, sub_pos, probit_lt_iff hF_lo hF_hi hH_lo hH_hi]

end Recovery

section OperatingCharacteristic

/-! ## Operating characteristic `β` and unbiased observers -/

/-- **β (operating likelihood ratio at criterion)**: `β = exp(d' · c)`.

    The likelihood ratio of the signal vs noise distribution evaluated at the
    decision criterion `c`. Standard SDT-observer diagnostic alongside `(d', c)`:
    `β > 1` indicates a conservative observer (prefers "noise"), `β < 1` liberal
    (prefers "signal"), `β = 1` unbiased. -/
noncomputable def SDTModel.beta (m : SDTModel) : ℝ :=
  Real.exp (m.dPrime * m.criterion)

/-- `β` is always positive (being an exponential). -/
theorem SDTModel.beta_pos (m : SDTModel) : 0 < m.beta := exp_pos _

/-- Unbiased observer: `criterion = 0` (equivalently `β = 1` when `d' > 0`).

    Mathlib `Is*` Prop-predicate convention. -/
def SDTModel.IsUnbiased (m : SDTModel) : Prop := m.criterion = 0

/-- Unbiased implies `β = 1`. The converse fails when `d' = 0` (then
    `β = 1` for any `c`); for non-trivial discriminators see
    `isUnbiased_iff_beta_eq_one_of_pos`. -/
theorem SDTModel.IsUnbiased.beta_eq_one {m : SDTModel} (h : m.IsUnbiased) :
    m.beta = 1 := by
  simp [SDTModel.beta, show m.criterion = 0 from h]

/-- For non-trivial discriminators (`d' > 0`), unbiased ↔ `β = 1`. -/
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

/-- **Unbiased ↔ `H + F = 1`**: a clean observable characterization of the
    unbiased criterion.

    Under the symmetric parameterization, `H + F = Φ(d'/2 - c) + Φ(-d'/2 - c)`,
    and by the identity `Φ(a) + Φ(-a-2c) = 1` (when `c = 0`, this collapses to
    `Φ(a) + Φ(-a) = 1`), this sum equals 1 exactly when `c = 0`.

    The forward direction is easy; the backward needs `d' > 0` (otherwise `H = F`
    for any c and `H + F = 2H` constrains `H = 1/2` rather than `c = 0`). -/
theorem SDTModel.IsUnbiased.hit_plus_fa_eq_one {m : SDTModel} (h : m.IsUnbiased) :
    m.hitRate + m.falseAlarmRate = 1 := by
  have hc : m.criterion = 0 := h
  simp only [SDTModel.hitRate, SDTModel.falseAlarmRate, SDTModel.tailProb,
    hc, zero_sub, zero_add, sub_neg_eq_add]
  have hneg : 1 - normalCDF (-(m.dPrime / 2)) = normalCDF (m.dPrime / 2) := by
    rw [normalCDF_neg]; ring
  rw [hneg]; ring

/-- **Proportion correct exceeds 1/2 for unbiased non-trivial observers.**

    Combining `H + F = 1` (from `IsUnbiased.hit_plus_fa_eq_one`) with
    `tailProb_strictMono` applied to `-d'/2 < d'/2` (the `F < H` content of
    `roc_above_diagonal`, inlined here to avoid forward reference):
    `proportionCorrect = (H + 1 - F)/2 > 1/2` follows by `linarith`. -/
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

/-- The ROC curve for a given `d'`: maps false alarm rate to hit rate as the
    criterion varies. Parameterized by criterion `c`:

      `(F(c), H(c)) = (1 - Φ(c + d'/2), 1 - Φ(c - d'/2))`

    Eliminating `c`: `H = Φ(Φ⁻¹(F) + d')`, equivalently
    `H = 1 - Φ(Φ⁻¹(1 - F) - d')`. We define the ROC curve directly as a
    function of the false alarm rate. -/
noncomputable def rocCurve (dPrime : ℝ) (falseAlarmRate : ℝ) : ℝ :=
  1 - normalCDF (probit (1 - falseAlarmRate) - dPrime)

/-- For `d' = 0`, the ROC curve is the diagonal: `H = F` (chance performance). -/
theorem roc_diagonal (f : ℝ) (hf : 0 < f) (hf' : f < 1) :
    rocCurve 0 f = f := by
  simp only [rocCurve, sub_zero]
  have h1f0 : 0 < 1 - f := by linarith
  have h1f1 : 1 - f < 1 := by linarith
  rw [probit_spec h1f0 h1f1]; ring

/-- For `d' > 0`, the ROC curve lies above the diagonal: `H > F`.

    Direct corollary of `tailProb_strictMono`: the signal+noise mean `+d'/2`
    exceeds the noise mean `-d'/2` whenever `d' > 0`, so the hit-rate tail
    exceeds the false-alarm tail. -/
theorem roc_above_diagonal (m : SDTModel) (hd : 0 < m.dPrime) :
    m.falseAlarmRate < m.hitRate :=
  m.tailProb_strictMono (by linarith : -(m.dPrime / 2) < m.dPrime / 2)

/-! Note: monotonicity of the equal-variance AUC `Φ(d'/√2)` in `d'` lives in
`GaussianChoice.lean` as `SDTModel.twoAFC_mono`; the AUC integral identity
`∫₀¹ rocCurve d' f df = Φ(d'/√2)` (Green & Swets 1966 @cite{green-swets-1966})
is correct but unproved — integrating `rocCurve` requires additional measure-
theoretic infrastructure not currently developed. -/

end ROC

section LuceEmbedding

/-! ## SDT as a Luce model — exact via McFadden's theorem

The SDT signal/noise choice is a binary Gumbel-Luce RUM: with utilities
`(d' · x, 0)` and unit Gumbel scale `β = 1`, the McFadden integral reduces
to the SDT Luce policy exactly. The signal-probability and odds-ratio
properties below are immediate corollaries of `mcfaddenIntegral_binary` and
`RationalAction.fromGumbelRUM_policy`. -/

/-- The Gaussian likelihood ratio at observation `x`, given `d'`, in the
    symmetric parameterization:

      `L(x) = f_{sN}(x) / f_N(x) = exp(d' · x)`

    where `f_N ~ N(-d'/2, 1)`, `f_{sN} ~ N(d'/2, 1)`, and `x` is the raw
    internal response (measured from the midpoint between the two means).
    Derivation:
      `log L(x) = log f_{sN}(x) - log f_N(x)`
               `= [-(x - d'/2)²/2] - [-(x + d'/2)²/2]`
               `= ((x + d'/2)² - (x - d'/2)²) / 2 = d' · x`.

    The user-facing form is `SDTModel.likelihoodRatioAt` (namespaced on the
    model); this bare form takes `dPrime` as a free parameter and is the
    underlying definition. -/
noncomputable def likelihoodRatio (dPrime x : ℝ) : ℝ :=
  Real.exp (dPrime * x)

/-- The likelihood ratio is always positive (being an exponential). -/
theorem likelihoodRatio_pos (dPrime x : ℝ) : 0 < likelihoodRatio dPrime x :=
  exp_pos _

/-- The Gaussian likelihood ratio at observation `x` for an SDT model. -/
noncomputable def SDTModel.likelihoodRatioAt (m : SDTModel) (x : ℝ) : ℝ :=
  likelihoodRatio m.dPrime x

/-- Always positive. -/
theorem SDTModel.likelihoodRatioAt_pos (m : SDTModel) (x : ℝ) :
    0 < m.likelihoodRatioAt x := likelihoodRatio_pos _ _

/-- SDT embedded as a binary Gumbel-Luce RUM (McFadden's theorem).

    Construction: utilities `u(signal) = d' · x`, `u(noise) = 0`, with unit
    Gumbel scale (`β = 1`). By `RationalAction.fromGumbelRUM`, the score is
    `exp(u_i / β) = exp(d' · x)` for signal and `exp(0) = 1` for noise — i.e.,
    `(L(x), 1)`, the Bayesian-posterior-odds form under uniform prior.

    The Luce policy `P("signal" | x) = L(x) / (L(x) + 1)` is then immediate
    from `mcfaddenIntegral_binary` (proved as `toLuceAt_signal_prob` below).

    *Note*: the construction depends on `m.dPrime` and the observation `x`,
    not on `m.criterion`. The criterion enters only at decision time (the
    observer's response rule); the Luce score structure encodes the
    Bayesian likelihood, which is criterion-independent. -/
noncomputable def SDTModel.toLuceAt (m : SDTModel) (x : ℝ) :
    RationalAction Unit (Fin 2) :=
  RationalAction.fromGumbelRUM (fun i : Fin 2 => if i = 0 then m.dPrime * x else 0) 1

/-- The score on "signal" (action 0) is the likelihood ratio. -/
@[simp]
theorem SDTModel.toLuceAt_score_signal (m : SDTModel) (x : ℝ) :
    (m.toLuceAt x).score () (0 : Fin 2) = m.likelihoodRatioAt x := by
  simp [SDTModel.toLuceAt, RationalAction.fromGumbelRUM,
        SDTModel.likelihoodRatioAt, likelihoodRatio]

/-- The score on "noise" (action 1) is `1` (the Gumbel-RUM score with utility 0). -/
@[simp]
theorem SDTModel.toLuceAt_score_noise (m : SDTModel) (x : ℝ) :
    (m.toLuceAt x).score () (1 : Fin 2) = 1 := by
  simp [SDTModel.toLuceAt, RationalAction.fromGumbelRUM]

/-- The Luce odds ratio `score(signal) / score(noise)` equals the likelihood
    ratio — the core SDT/Luce identification.

    Now an immediate corollary of the score-component lemmas. -/
theorem SDTModel.toLuceAt_odds_ratio (m : SDTModel) (x : ℝ) :
    (m.toLuceAt x).score () (0 : Fin 2) /
    (m.toLuceAt x).score () (1 : Fin 2) =
    m.likelihoodRatioAt x := by
  rw [m.toLuceAt_score_signal, m.toLuceAt_score_noise, div_one]

/-- The Luce signal probability `L(x) / (L(x) + 1)`, derived as a corollary of
    `mcfaddenIntegral_binary` via `RationalAction.fromGumbelRUM_policy`. -/
theorem SDTModel.toLuceAt_signal_prob (m : SDTModel) (x : ℝ) :
    (m.toLuceAt x).policy () (0 : Fin 2) =
    m.likelihoodRatioAt x / (m.likelihoodRatioAt x + 1) := by
  rw [SDTModel.toLuceAt, RationalAction.fromGumbelRUM_policy _ one_pos,
      mcfaddenIntegral_binary _ one_pos]
  have h01 : ¬(1 : Fin 2) = (0 : Fin 2) := by decide
  simp only [Fin.isValue, ↓reduceIte, h01, sub_zero, div_one, logistic,
             SDTModel.likelihoodRatioAt, likelihoodRatio]
  rw [show m.dPrime * x = -(-(m.dPrime * x)) from by ring,
      show -(-(m.dPrime * x)) = -(-1 * (m.dPrime * x)) from by ring,
      neg_mul, one_mul, neg_neg]
  -- Goal: 1 / (1 + exp(-(d'·x))) = exp(d'·x) / (exp(d'·x) + 1)
  have hpos : (0 : ℝ) < Real.exp (m.dPrime * x) := exp_pos _
  field_simp
  rw [Real.exp_neg]
  field_simp

end LuceEmbedding

section BayesianInterpretation

/-! ## Bayesian posterior interpretation

The SDT Luce policy is exactly the Bayesian posterior on "signal present"
under uniform prior odds. Under non-uniform prior `π_S` for signal, the
posterior is `π_S · L(x) / (π_S · L(x) + (1 - π_S))` — the same formula but
with prior-weighted likelihoods. With `π_S = 1/2`, this reduces to
`L(x) / (L(x) + 1) = (m.toLuceAt x).policy () 0`.

### Why `posteriorAt` is not implemented via `PMF.posterior`

The SDT observer's hypothesis space is binary (`{signal, noise} = Fin 2`)
and finite, but the *observation* `x : ℝ` is *continuous* (a real-valued
internal response). Mathlib's `PMF.posterior` (`Core/Probability/PMFPosterior.lean`)
operates on countable observation spaces; it does not natively handle
continuous observations. The right mathlib substrate for the continuous
binary case is `MeasureTheory.Kernel` + `condCDF`, which we have not set
up here. Until that infrastructure is in place, `SDTModel.posteriorAt`
provides the closed-form Bayes' rule formula directly — *not* a parallel
implementation of `PMF.posterior`'s discrete machinery, but a *genuinely
distinct* abstraction for the continuous case (cf. `Finset.sum` vs
`Measure.integral` in mathlib: same idea, different abstractions for
different domains). -/

variable (m : SDTModel)

/-- The Bayesian posterior `P(signal | x)` under prior `priorSignal ∈ [0, 1]`
    for "signal present", with Gaussian likelihoods determined by `m.dPrime`.

    `P(signal | x) = π_S · L(x) / (π_S · L(x) + (1 - π_S))`

    by Bayes' rule applied to the binary hypothesis `{signal, noise}` with
    likelihood ratio `L(x) = f_{sN}(x) / f_N(x) = exp(m.dPrime · x)`. -/
noncomputable def SDTModel.posteriorAt (x : ℝ) (priorSignal : ℝ) : ℝ :=
  priorSignal * m.likelihoodRatioAt x /
    (priorSignal * m.likelihoodRatioAt x + (1 - priorSignal))

/-- Helper: for any positive real `L`, the uniform-prior posterior reduces to
    `L / (L + 1)`. Used by both `posteriorAt_uniform` and
    `posterior_gt_half_iff_pos_obs`. -/
private lemma posterior_uniform_eq_div {L : ℝ} (hL : 0 < L) :
    (1 : ℝ) / 2 * L / ((1 : ℝ) / 2 * L + (1 - 1 / 2)) = L / (L + 1) := by
  have hLp1 : (0 : ℝ) < L + 1 := by linarith
  have hLp1_ne : L + 1 ≠ 0 := ne_of_gt hLp1
  field_simp; ring

/-- Helper: `1/2 < L / (L + 1) ↔ 1 < L` for positive `L`. The Bayes-optimal
    threshold criterion in algebraic form. -/
private lemma half_lt_div_add_one_iff {L : ℝ} (hL : 0 < L) :
    1 / 2 < L / (L + 1) ↔ 1 < L := by
  have hLp1 : (0 : ℝ) < L + 1 := by linarith
  rw [lt_div_iff₀ hLp1]; constructor <;> intro h <;> linarith

/-- **Luce policy = Bayesian posterior under uniform prior.**

    With prior `π_S = 1/2`, the Bayesian posterior `P(signal | x)` reduces to
    `L(x) / (L(x) + 1)`, which is exactly `(m.toLuceAt x).policy () 0` by
    `toLuceAt_signal_prob`.

    This is the *deepest* connection between SDT and Bayesian inference:
    Luce probability matching on the binary detection task IS Bayes' rule
    under uniform priors. -/
theorem SDTModel.posteriorAt_uniform (x : ℝ) :
    m.posteriorAt x (1/2) = (m.toLuceAt x).policy () (0 : Fin 2) := by
  rw [m.toLuceAt_signal_prob, SDTModel.posteriorAt]
  exact posterior_uniform_eq_div (m.likelihoodRatioAt_pos x)

/-- **Bayes-optimal threshold under uniform prior**: the posterior on "signal"
    exceeds 1/2 iff the observation is positive (when `d' > 0`).

    Equivalently: the Bayes-optimal decision rule "respond signal iff
    posterior > 1/2" coincides with the SDT criterion-zero rule "respond
    signal iff x > 0" — i.e., `criterion = 0` is Bayes-optimal under uniform
    prior and 0–1 loss.

    Under non-uniform prior odds `π_N / π_S`, the optimal threshold is
    `c* = log(π_N / π_S) / d'` (UNVERIFIED: standard SDT result, see
    @cite{green-swets-1966} and @cite{macmillan-creelman-2005} ch. 1; not
    formalized here — would require continuous Bayesian-decision
    infrastructure). -/
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
probabilities (McFadden's theorem; see `gumbelMaxProb_is_mcfaddenIntegral`
in `GumbelLuce.lean`). The Gaussian model gives `Φ`. These agree up to the
numerical approximation `Φ ≈ logistic`.

The constant `k = π/√3` equals `thurstoneLuceK(1/√2)`, unifying the SDT
and Thurstone parameterizations — proved as
`logisticApproxConst_eq_thurstoneLuceK` in `GaussianChoice.lean`.

The variance-matching constant `π/√3 ≈ 1.8138` is exact (logistic has
variance `π²/3`, so scaling `Φ` by `π/√3` matches unit-variance normal).
The optimal sup-norm constant for `Φ(x) ≈ σ(k · x)` is approximately
`1.7009` (Page 1977). We use `π/√3` rather than the sup-norm optimum
because it has a clean variance-matching derivation and equals
`thurstoneLuceK(1/√2)`. UNVERIFIED: the sup-error figure `≈ 0.023` is
quoted from secondary sources; verify against Bowling et al. 2009 or
Page 1977 before relying on it. -/

/-- The logistic approximation constant: `k = π/√3 ≈ 1.814`.

    The variance-matching scale factor between the standard normal and
    standard logistic distributions: the standard logistic has variance
    `π²/3`, so `Φ(x) ≈ logistic(x · π/√3)`. -/
noncomputable def logisticApproxConst : ℝ := Real.pi / Real.sqrt 3

/-- The logistic approximation constant is positive. -/
theorem logisticApproxConst_pos : 0 < logisticApproxConst :=
  div_pos Real.pi_pos (Real.sqrt_pos.mpr (by norm_num))

end LogisticApproximation

end Core
