import Linglib.Processing.Psychophysics.Psychophysics
import Linglib.Core.Probability.Choice.ChoiceApproximations

/-!
# Psychophysical Choice Bridge [luce-1959]

Connects two independently formalized modules that both operate on
Luce ratio scales:

- **Psychophysics** (§2.B–C): Stevens' power law `ψ(s) = k · sⁿ` and
  multidimensional multiplicative decomposition.
- **ChoiceApproximations** (§1.G): Pairwise choice probabilities, JND
  thresholds, semiorder structure, and the trace ordering.

The bridge connects them via three results:

1. **Stevens choiceProb = pairwiseProb**: Stevens' power-law choice
   probability is literally `pairwiseProb` on the power scale `v(s) = sⁿ`.
2. **Weber fraction from JND**: The JND threshold π translates to a
   just-noticeable intensity ratio `(π/(1-π))^(1/n)`, yielding a Weber-like
   law: `Δs/s = (π/(1-π))^(1/n) - 1`.
3. **Trace = intensity ordering**: The trace ordering from §1.G on the
   power scale recovers the physical intensity ordering.
-/

namespace Core

open Real BigOperators Finset

-- ============================================================================
-- §1. Stevens' choiceProb = pairwiseProb on the power scale
-- ============================================================================

/-- Stevens' power-law choice probability is literally the pairwise choice
    probability from §1.G with scale function `v(s) = sⁿ`.

    `StevensScale.choiceProb σ s₁ s₂ = s₁ⁿ / (s₁ⁿ + s₂ⁿ)`
    `pairwiseProb (· ^ σ.n) s₁ s₂ = s₁ⁿ / (s₁ⁿ + s₂ⁿ)`

    This identity hooks Stevens scales into the entire §1.G infrastructure:
    JND relations, semiorder structure, and the trace ordering all apply
    directly to psychophysical scales. -/
theorem stevens_eq_pairwiseProb (σ : StevensScale) (s₁ s₂ : ℝ) :
    σ.choiceProb s₁ s₂ = pairwiseProb (· ^ σ.n) s₁ s₂ := by
  simp only [StevensScale.choiceProb, pairwiseProb]

-- ============================================================================
-- §2. JND relations on Stevens scales: Weber-like law
-- ============================================================================

/-- The JND "discriminably preferred" relation on a Stevens scale:
    stimulus `s₁` is discriminably preferred to `s₂` at threshold `π` iff
    `P(s₁, s₂) = s₁ⁿ/(s₁ⁿ+s₂ⁿ) > π`.

    This is just `jndL` from §1.G applied to the power scale. -/
theorem stevens_jndL_iff (σ : StevensScale) (thr : ℝ) (s₁ s₂ : ℝ) :
    jndL (· ^ σ.n) thr s₁ s₂ ↔ thr < σ.choiceProb s₁ s₂ := by
  simp only [jndL, stevens_eq_pairwiseProb]

/-- The JND "indistinguishable" relation on a Stevens scale:
    stimuli are indistinguishable iff `1-π ≤ P(s₁,s₂) ≤ π`. -/
theorem stevens_jndI_iff (σ : StevensScale) (thr : ℝ) (s₁ s₂ : ℝ) :
    jndI (· ^ σ.n) thr s₁ s₂ ↔
    (1 - thr ≤ σ.choiceProb s₁ s₂ ∧ σ.choiceProb s₁ s₂ ≤ thr) := by
  simp only [jndI, stevens_eq_pairwiseProb]

/-- **Weber-like ratio from JND**: if `s₁` is discriminably preferred to `s₂`
    at threshold `π` under a Stevens scale with exponent `n`, then the
    intensity ratio `s₁/s₂` exceeds `(π/(1-π))^(1/n)`.

    This is the psychophysical content of the JND: the just-noticeable
    intensity ratio `(π/(1-π))^(1/n)` is the Weber fraction + 1.

    For `n = 1` (linear scale): JND ratio = `π/(1-π)`
    For large `n`: JND ratio → 1 (finer discrimination)
    For small `n`: JND ratio → ∞ (coarser discrimination) -/
theorem stevens_jndL_intensity_ratio (σ : StevensScale) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1)
    {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (hL : jndL (· ^ σ.n) thr s₁ s₂) :
    (thr / (1 - thr)) ^ (1 / σ.n) < s₁ / s₂ := by
  simp only [jndL, pairwiseProb] at hL
  have hp₁ : 0 < s₁ ^ σ.n := rpow_pos_of_pos h₁ σ.n
  have hp₂ : 0 < s₂ ^ σ.n := rpow_pos_of_pos h₂ σ.n
  have hd : 0 < s₁ ^ σ.n + s₂ ^ σ.n := add_pos hp₁ hp₂
  rw [lt_div_iff₀ hd] at hL
  have h1mt : 0 < 1 - thr := by linarith
  have hthr_ratio_pos : 0 < thr / (1 - thr) := div_pos (by linarith) h1mt
  have h_ratio : thr / (1 - thr) < (s₁ / s₂) ^ σ.n := by
    rw [div_rpow (le_of_lt h₁) (le_of_lt h₂), div_lt_div_iff₀ h1mt hp₂]; nlinarith
  have h5 := rpow_lt_rpow (le_of_lt hthr_ratio_pos) h_ratio (div_pos one_pos σ.hn_pos)
  rw [← rpow_mul (le_of_lt (div_pos h₁ h₂)), mul_one_div_cancel (ne_of_gt σ.hn_pos),
    rpow_one] at h5
  exact h5

-- ============================================================================
-- §3. Trace ordering = intensity ordering for power scales
-- ============================================================================

/-- The trace ordering from §1.G on the Stevens power scale recovers the
    physical intensity ordering: `s₁ ≥_T s₂` iff `s₁ ≥ s₂`.

    For `v(s) = sⁿ` with `n > 0` and positive stimuli, `s₂ⁿ ≤ s₁ⁿ ↔ s₂ ≤ s₁`.
    The trace extracts pairwise dominance over all comparisons, but for
    a monotone power scale this reduces to the physical ordering.

    The trace is restricted to positive comparison stimuli because `rpow`
    on negative bases is defined via complex exponentiation, so `z ^ n`
    for `z < 0` can be negative (e.g., `rpow (-1) 1 = -1`), violating
    the positivity assumptions that underlie the choice-probability model.
    Stimulus intensities are inherently positive reals. -/
theorem stevens_trace_iff_intensity (σ : StevensScale) {s₁ s₂ : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    (∀ z : ℝ, 0 < z → pairwiseProb (· ^ σ.n) s₂ z ≤ pairwiseProb (· ^ σ.n) s₁ z) ↔
    s₂ ≤ s₁ := by
  constructor
  · -- Forward: positive-restricted trace → s₂ ≤ s₁
    -- Specialize at z = s₁ (positive): P(s₂, s₁) ≤ P(s₁, s₁) = 1/2
    intro htrace
    by_contra hlt; push Not at hlt
    have hpow := rpow_lt_rpow (le_of_lt h₁) hlt σ.hn_pos
    have hz := htrace s₁ h₁
    simp only [pairwiseProb] at hz
    have hd₁ : 0 < s₁ ^ σ.n := rpow_pos_of_pos h₁ σ.n
    have hd₂ : 0 < s₂ ^ σ.n := rpow_pos_of_pos h₂ σ.n
    have : s₁ ^ σ.n / (s₁ ^ σ.n + s₁ ^ σ.n) = 1 / 2 := by
      field_simp; ring
    rw [this] at hz
    have : 1 / 2 < s₂ ^ σ.n / (s₂ ^ σ.n + s₁ ^ σ.n) := by
      rw [lt_div_iff₀ (add_pos hd₂ hd₁)]
      linarith
    linarith
  · -- Backward: s₂ ≤ s₁ → positive-restricted trace
    -- s₂ⁿ ≤ s₁ⁿ, and for z > 0 we have zⁿ > 0, so cross-multiplication works:
    -- s₂ⁿ/(s₂ⁿ+zⁿ) ≤ s₁ⁿ/(s₁ⁿ+zⁿ) ↔ s₂ⁿ·zⁿ ≤ s₁ⁿ·zⁿ (true since s₂ⁿ ≤ s₁ⁿ, zⁿ > 0).
    intro hle z hz
    simp only [pairwiseProb]
    have hp₁ : 0 < s₁ ^ σ.n := rpow_pos_of_pos h₁ σ.n
    have hp₂ : 0 < s₂ ^ σ.n := rpow_pos_of_pos h₂ σ.n
    have hpz : 0 < z ^ σ.n := rpow_pos_of_pos hz σ.n
    have hpow : s₂ ^ σ.n ≤ s₁ ^ σ.n :=
      rpow_le_rpow (le_of_lt h₂) hle (le_of_lt σ.hn_pos)
    rw [div_le_div_iff₀ (add_pos hp₂ hpz) (add_pos hp₁ hpz)]
    nlinarith [mul_le_mul_of_nonneg_right hpow (le_of_lt hpz)]

end Core
