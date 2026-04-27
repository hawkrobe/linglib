import Linglib.Core.Agent.SignalDetection
import Linglib.Core.Agent.Thurstone
import Linglib.Core.Agent.GumbelLuce
import Linglib.Core.Agent.Psychophysics

/-!
# Gaussian Choice Bridge @cite{luce-1959}

Connects the two Gaussian choice models formalized independently in
`SignalDetection.lean` (§2.E) and `Thurstone.lean` (§2.D):

- **Thurstone Case V** (§2.D): Paired comparison — each stimulus evokes a
  Gaussian discriminal process; choice probability is `Φ((u(a)-u(b))/(σ√2))`.
- **SDT** (§2.E): Detection — a single observation is compared to a criterion;
  hit rate is `1 - Φ(c - d'/2) = Φ(d'/2 - c)`.

Luce (§2.E, p. 60) notes that SDT is "essentially Thurstone's discriminal
process theory applied to the two-alternative detection context." This file
makes that connection precise via four results:

1. **SDT as Thurstone (2AFC)**: The two-alternative forced choice (2AFC)
   correct-response probability `Φ(d'/√2)` equals Thurstone's `choiceProb`
   for signal vs noise with unit per-stimulus variance.
2. **Yes/No SDT as Thurstone**: The yes/no hit rate `Φ(d'/2 - c)` equals
   Thurstone's `choiceProb` with `σ = 1/√2`.
3. **Logistic constant unification**: SDT's `logisticApproxConst = π/√3`
   equals Thurstone's `thurstoneLuceK(1/√2)`.
4. **Shared softmax embedding**: Both approximate the same `RationalAction`
   under the logistic-normal approximation.
-/

namespace Core

open Real BigOperators Finset

/-! ## Two-Alternative Forced Choice (2AFC) as Thurstone -/

/-- Two-alternative forced choice (2AFC) correct-response probability.

    In 2AFC, the observer sees two intervals — one containing signal+noise
    (from N(d'/2, 1)) and one containing noise only (from N(-d'/2, 1)) —
    and identifies which had the signal. The correct response probability is:

    `P(correct) = P(X_signal > X_noise) = Φ(d' / √2)`

    since X_signal - X_noise ~ N(d', 2), so (X_signal - X_noise)/√2 ~ N(d'/√2, 1). -/
noncomputable def SDTModel.twoAFC (m : SDTModel) : ℝ :=
  normalCDF (m.dPrime / Real.sqrt 2)

/-- 2AFC probability is at least 1/2 when `d' ≥ 0`: the observer performs
    at or above chance. The `0 ≤ m.dPrime` hypothesis is explicit (not a
    structure invariant); see the docstring on `SDTModel`. -/
theorem SDTModel.twoAFC_ge_half (m : SDTModel) (h_nonneg : 0 ≤ m.dPrime) :
    1 / 2 ≤ m.twoAFC := by
  simp only [twoAFC]
  rcases eq_or_lt_of_le h_nonneg with h | h
  · rw [← h, zero_div]; exact le_of_eq normalCDF_zero.symm
  · exact le_of_lt (normalCDF_pos_gt_half (div_pos h
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))))

/-- Construct a Thurstone Case V model for the 2AFC detection task.

    Signal and noise are treated as two stimuli with scale values `d'/2`
    and `-d'/2`, both with unit discriminal dispersion (`σ = 1`).
    Fin 2: `0` = signal, `1` = noise. -/
noncomputable def SDTModel.asThurstone2AFC (m : SDTModel) : ThurstoneCaseV (Fin 2) where
  scale i := if i = 0 then m.dPrime / 2 else -(m.dPrime / 2)
  sigma := 1
  sigma_pos := one_pos

/-- **SDT 2AFC = Thurstone Case V**: the 2AFC correct-response probability
    equals the Thurstone choice probability for signal vs noise.

    Both reduce to `Φ(d' / √2)`:
    - 2AFC: `Φ(d' / √2)` (by definition)
    - Thurstone: `Φ((d'/2 - (-d'/2)) / (1 · √2)) = Φ(d' / √2)` -/
theorem SDTModel.twoAFC_eq_thurstone (m : SDTModel) :
    m.twoAFC = m.asThurstone2AFC.choiceProb 0 1 := by
  simp only [twoAFC, asThurstone2AFC, ThurstoneCaseV.choiceProb]
  have h01 : ¬(1 : Fin 2) = (0 : Fin 2) := by decide
  simp only [h01, ↓reduceIte]
  congr 1
  ring_nf

/-! ## Yes/No SDT as Thurstone -/

/-- Construct a Thurstone Case V model for the yes/no SDT task.

    The yes/no task (observe, then decide signal vs noise) is equivalent
    to a Thurstone model with `σ = 1/√2` (so that `σ√2 = 1`), where:
    - `scale(signal) = d'/2 - c` (effective signal advantage)
    - `scale(noise) = 0`
    Fin 2: `0` = signal, `1` = noise. -/
noncomputable def SDTModel.asThurstoneYesNo (m : SDTModel) : ThurstoneCaseV (Fin 2) where
  scale i := if i = 0 then m.dPrime / 2 - m.criterion else 0
  sigma := 1 / Real.sqrt 2
  sigma_pos := div_pos one_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))

/-- **Yes/No SDT = Thurstone**: the hit rate equals the Thurstone choice
    probability for the yes/no model.

    SDT hit rate: `1 - Φ(c - d'/2) = Φ(d'/2 - c)` (by CDF symmetry).
    Thurstone with σ = 1/√2: `Φ((d'/2 - c) / ((1/√2) · √2)) = Φ(d'/2 - c)`.

    The key identity is `(1/√2) · √2 = 1`, so the Thurstone denominator
    is 1 and the two expressions coincide. -/
theorem SDTModel.hitRate_eq_thurstone (m : SDTModel) :
    m.hitRate = m.asThurstoneYesNo.choiceProb 0 1 := by
  simp only [SDTModel.hitRate, SDTModel.tailProb, asThurstoneYesNo,
             ThurstoneCaseV.choiceProb]
  have h01 : ¬(1 : Fin 2) = (0 : Fin 2) := by decide
  simp only [h01, ↓reduceIte, sub_zero]
  -- Goal: 1 - normalCDF (c - d'/2) = normalCDF ((d'/2 - c) / ((1/√2) * √2))
  -- Step 1: simplify (1/√2) * √2 = 1
  have h_sqrt2_ne : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  have h_denom : (1 : ℝ) / Real.sqrt 2 * Real.sqrt 2 = 1 := by
    rw [one_div, inv_mul_cancel₀ h_sqrt2_ne]
  rw [h_denom, div_one]
  -- Step 2: 1 - Φ(c - d'/2) = Φ(d'/2 - c) by normalCDF symmetry
  rw [show m.criterion - m.dPrime / 2 = -(m.dPrime / 2 - m.criterion) from by ring,
      normalCDF_neg]
  -- Goal: 1 - (1 - normalCDF (d'/2 - c)) = normalCDF (d'/2 - c)
  linarith

/-! ## Logistic Approximation Constants -/

/-- The SDT logistic approximation constant `π/√3` equals Thurstone's
    `thurstoneLuceK` when `σ = 1/√2`.

    This is because:
    `thurstoneLuceK(1/√2) = π / ((1/√2) · √6) = π · √2 / √6 = π / √3`

    The identity `√2 / √6 = 1/√3` follows from `√2 · √3 = √6`.

    Significance: the logistic approximation that connects SDT to the Luce
    model (§2.E) is exactly the same as the approximation that connects
    Thurstone to the Luce model (§2.D), when we use the yes/no SDT
    parameterization (σ = 1/√2). -/
theorem logisticApproxConst_eq_thurstoneLuceK :
    logisticApproxConst = thurstoneLuceK (1 / Real.sqrt 2) := by
  -- π/√3 = π / ((1/√2) · √6)
  -- (1/√2) · √6 = √6/√2 = √(6/2) = √3
  simp only [logisticApproxConst, thurstoneLuceK]
  congr 1
  -- Goal: √3 = (1 / √2) * √6
  rw [div_mul_eq_mul_div, one_mul]
  rw [show (6 : ℝ) = 3 * 2 from by norm_num]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [mul_div_cancel_of_imp]
  intro h
  exact absurd h (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))

/-! ## Shared Softmax Embedding -/

/-- 2AFC models with different `d'` can be compared via the Thurstone ordering.

    Since `twoAFC = Thurstone.choiceProb`, and Thurstone satisfies strong
    stochastic transitivity, higher `d'` implies higher 2AFC `P(correct)`.

    Proof: `d₁' > d₂'` implies `scale(signal) - scale(noise) = d'` is larger,
    so the Thurstone argument `d'/√2` is larger, and `Φ` is strictly monotone.

    *Connection to AUC*: under the equal-variance Gaussian SDT model, the
    area under the ROC curve equals `Φ(d'/√2)` (@cite{green-swets-1966};
    @cite{macmillan-creelman-2005}, ch. 3). This theorem therefore proves
    that AUC is strictly monotone in `d'`. The AUC integral identity itself
    — `∫₀¹ rocCurve d' f df = Φ(d'/√2)` — is correct but unproved here;
    integrating `rocCurve` requires additional measure-theoretic
    infrastructure not currently developed. -/
theorem SDTModel.twoAFC_mono (m₁ m₂ : SDTModel)
    (h : m₁.dPrime < m₂.dPrime) :
    m₁.twoAFC < m₂.twoAFC := by
  simp only [twoAFC]
  exact normalCDF_strictMono (by
    exact div_lt_div_of_pos_right h
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))

/-! ## Random Utility Model Unification -/

/-!
## RUM Unification

Both Thurstone and Luce choice models are Random Utility Models (RUMs) —
they differ only in the noise distribution:

| Model       | Noise Distribution | Choice Probability | Reference |
|-------------|--------------------|--------------------|-----------|
| Thurstone V | Gaussian(0, σ²)   | `Φ((u_a-u_b)/(σ√2))` | `Thurstone.lean` |
| Gumbel-Luce | Gumbel(0, β)      | `logistic((u_a-u_b)/β)` | `GumbelLuce.lean` |

The Gumbel-Luce model gives **exactly** the softmax (Luce) choice rule
(McFadden's theorem, `mcfaddenIntegral_eq_softmax`). The Thurstone model
gives the normal CDF. These agree up to the Gaussian-logistic approximation
`Φ(y·√3/π) ≈ logistic(y)` (max error ~0.023, variance matching;
see `thurstone_luce_identity`).

The constant `k = π/(σ√6)` that appears in the Thurstone-Luce approximation
(`thurstoneLuceK`) is the scale matching between Gaussian and Gumbel noise:
it equates the variances `σ² · 2` (Gaussian difference) and `β² · π²/3`
(logistic/Gumbel difference).
-/

/-- **Gumbel-Luce binary = logistic (exact)**: A Gumbel RUM with utilities
    `[d'/2, -d'/2]` and scale `β` gives choice probability `logistic(d'/β)`.

    Compare with Thurstone Case V (`hitRate_eq_thurstone`), which gives
    `Φ(d'/(σ√2))` — the same functional form but with the normal CDF
    instead of logistic.

    The two models are both RUMs; they agree when `Φ ≈ logistic`, i.e.,
    when the variance-matched scale `β = σ√6/π` (see `thurstoneLuceK`). -/
theorem gumbelRUM_binary_eq_logistic (d' β : ℝ) (hβ : 0 < β) :
    mcfaddenIntegral (λ i : Fin 2 => if i = 0 then d' / 2 else -(d' / 2)) β 0
    = logistic (d' / β) := by
  rw [mcfaddenIntegral_binary _ hβ]
  congr 1
  simp only [↓reduceIte]
  have h1 : ¬(1 : Fin 2) = (0 : Fin 2) := by decide
  simp only [h1, ↓reduceIte]
  ring

/-! ## Stevens → Thurstone → SDT chain

The two `Core/Agent/` psychophysics primitives — `StevensScale` (Stevens'
power law `ψ(s) = k · sⁿ`, the deterministic intensity-to-percept mapping) and
`SDTModel` (signal detection, the noisy discrimination operator) — sit in
*different regimes*:

- **Stevens** (`Psychophysics.lean`, @cite{luce-1959} §2.B): supra-threshold
  magnitude estimation. Maps physical intensity to perceived intensity
  deterministically.
- **Thurstone** (`Thurstone.lean`, @cite{thurstone-1927}; `luce-1959` §2.D):
  paired comparison via Gaussian discriminal processes. Adds noise on top
  of a scale value.
- **SDT** (`SignalDetection.lean`, @cite{green-swets-1966}): near-threshold
  binary discrimination. The yes/no specialization of Thurstone Case V.

This section composes the three: **Stevens scale + Gaussian noise = Thurstone
discriminal process; Thurstone for binary detection = SDT.** Concretely, an
observer with Stevens-scaled perception of intensity and Gaussian noise of
SD `σ` discriminating two stimuli `s_signal` vs `s_noise` is an SDT observer
with `d' = (ψ(s_signal) - ψ(s_noise)) / σ`.

This is the standard psychophysics chain; cf. @cite{macmillan-creelman-2005}
ch. 1 for the d′-vs-Stevens-Δψ relationship. -/

/-- **Stevens → Thurstone constructor**: Stevens' power-law perception with
    Gaussian discriminal dispersion `σ` is a Thurstone Case V model whose
    scale value at stimulus `s` is `ψ(s) = k · sⁿ`. -/
noncomputable def StevensScale.toThurstone (sc : StevensScale) (sigma : ℝ)
    (h_pos : 0 < sigma) : ThurstoneCaseV ℝ where
  scale s := sc.psi s
  sigma := sigma
  sigma_pos := h_pos

/-- The choice probability under Stevens-derived Thurstone is
    `Φ((ψ(s₁) - ψ(s₂)) / (σ · √2))` — the standard Thurstone Case V
    formula applied to the Stevens-transformed stimuli. -/
@[simp]
theorem StevensScale.toThurstone_choiceProb (sc : StevensScale) (sigma : ℝ)
    (h_pos : 0 < sigma) (s₁ s₂ : ℝ) :
    (sc.toThurstone sigma h_pos).choiceProb s₁ s₂ =
    normalCDF ((sc.psi s₁ - sc.psi s₂) / (sigma * Real.sqrt 2)) := by
  rfl

/-- **Stevens-derived d′**: the SDT sensitivity for discriminating two
    stimuli `s_signal` vs `s_noise` under Stevens scaling and Gaussian noise
    of SD `σ`. Equals `(ψ(s_signal) - ψ(s_noise)) / σ`.

    This is the standard psychophysics formula: noise-normalized difference
    of perceived intensities, exactly as `d'` is defined in SDT (mean
    difference in σ units). -/
noncomputable def StevensScale.dPrime (sc : StevensScale) (sigma : ℝ)
    (s_signal s_noise : ℝ) : ℝ :=
  (sc.psi s_signal - sc.psi s_noise) / sigma

/-- **Stevens → SDT 2AFC constructor**: Stevens-scaled perception of two
    stimuli `s_signal`, `s_noise` with Gaussian noise σ produces a
    zero-criterion (unbiased) SDT observer with `d'` from `StevensScale.dPrime`.

    The observer has zero criterion bias because 2AFC has no criterion
    parameter — both alternatives are presented and the observer picks
    the one with the larger discriminal sample. -/
noncomputable def StevensScale.toSDT (sc : StevensScale) (sigma : ℝ)
    (s_signal s_noise : ℝ) : SDTModel where
  dPrime := sc.dPrime sigma s_signal s_noise
  criterion := 0

/-- The Stevens-derived SDT observer is unbiased (zero criterion). -/
theorem StevensScale.toSDT_isUnbiased (sc : StevensScale) (sigma : ℝ)
    (s_signal s_noise : ℝ) : (sc.toSDT sigma s_signal s_noise).IsUnbiased :=
  rfl

/-- **Stevens-Thurstone-SDT chain coherence**: the 2AFC `P(correct)` predicted
    by the Stevens-derived SDT observer equals the Thurstone choice probability
    obtained by composing Stevens scaling with Gaussian noise.

    Both reduce to `Φ((ψ(s_signal) - ψ(s_noise)) / (σ · √2))`. The Stevens
    side computes via `SDTModel.twoAFC = Φ(d'/√2)` with `d' = Δψ/σ`; the
    Thurstone side computes via `(sc.toThurstone σ).choiceProb`. The two paths
    agree, validating the substrate composition. -/
theorem StevensScale.twoAFC_eq_thurstone (sc : StevensScale) (sigma : ℝ)
    (h_pos : 0 < sigma) (s_signal s_noise : ℝ) :
    (sc.toSDT sigma s_signal s_noise).twoAFC =
    (sc.toThurstone sigma h_pos).choiceProb s_signal s_noise := by
  simp only [SDTModel.twoAFC, StevensScale.toSDT, StevensScale.dPrime,
             StevensScale.toThurstone_choiceProb]
  congr 1
  rw [div_div, mul_comm sigma]

/-- Stevens-derived d′ is non-negative when `s_signal ≥ s_noise` and `σ > 0`,
    using `psi`'s monotonicity (Stevens' power law is monotone in stimulus
    intensity for positive stimuli with positive exponent). -/
theorem StevensScale.dPrime_nonneg (sc : StevensScale) (sigma : ℝ)
    (h_pos : 0 < sigma) {s_signal s_noise : ℝ}
    (h_noise : 0 < s_noise) (h_le : s_noise ≤ s_signal) :
    0 ≤ sc.dPrime sigma s_signal s_noise := by
  simp only [StevensScale.dPrime, StevensScale.psi]
  apply div_nonneg _ h_pos.le
  have : s_noise ^ sc.n ≤ s_signal ^ sc.n :=
    Real.rpow_le_rpow h_noise.le h_le sc.hn_pos.le
  nlinarith [sc.hk_pos]

end Core
