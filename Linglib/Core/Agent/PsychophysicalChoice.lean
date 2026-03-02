import Linglib.Core.Agent.Psychophysics
import Linglib.Core.Agent.ChoiceApproximations
import Linglib.Core.Agent.UtilityTheory

/-!
# Psychophysical Choice Bridge @cite{luce-1959}

Connects three independently formalized modules that all operate on
Luce ratio scales:

- **Psychophysics** (§2.B–C): Stevens' power law `ψ(s) = k · sⁿ` and
  multidimensional multiplicative decomposition.
- **ChoiceApproximations** (§1.G): Pairwise choice probabilities, JND
  thresholds, semiorder structure, and the trace ordering.
- **UtilityTheory** (Chapter 3): Gamble decomposition `v(aρb) = w(a,b)·φ(ρ)`
  and RSA utility as multiplicative factoring.

The bridge connects them via four results:

1. **Stevens choiceProb = pairwiseProb**: Stevens' power-law choice
   probability is literally `pairwiseProb` on the power scale `v(s) = sⁿ`.
2. **Weber fraction from JND**: The JND threshold π translates to a
   just-noticeable intensity ratio `(π/(1-π))^(1/n)`, yielding a Weber-like
   law: `Δs/s = (π/(1-π))^(1/n) - 1`.
3. **Trace = intensity ordering**: The trace ordering from §1.G on the
   power scale recovers the physical intensity ordering.
4. **RSA utility = two-dimensional psychophysics**: RSA's multiplicative
   score `informativity^α · exp(-α·cost)` is a two-factor psychophysical
   scale in the sense of §2.C's dimension independence.
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
  -- From jndL: s₁ⁿ/(s₁ⁿ+s₂ⁿ) > thr
  -- Rearranging: s₁ⁿ/s₂ⁿ > thr/(1-thr)
  -- Since s₁,s₂ > 0: (s₁/s₂)ⁿ > thr/(1-thr)
  -- Taking n-th root: s₁/s₂ > (thr/(1-thr))^(1/n)
  sorry

-- ============================================================================
-- §3. Trace ordering = intensity ordering for power scales
-- ============================================================================

/-- The trace ordering from §1.G on the Stevens power scale recovers the
    physical intensity ordering: `s₁ ≥_T s₂` iff `s₁ ≥ s₂`.

    For `v(s) = sⁿ` with `n > 0` and positive stimuli, `s₂ⁿ ≤ s₁ⁿ ↔ s₂ ≤ s₁`.
    The trace extracts pairwise dominance over all comparisons, but for
    a monotone power scale this reduces to the physical ordering.

    Note: proved directly rather than via `trace_iff_scale_ge`, because the
    latter requires `∀ a, 0 < v a` which fails for `v = (· ^ n)` on all of ℝ.
    Here we restrict to positive stimuli. -/
theorem stevens_trace_iff_intensity (σ : StevensScale) {s₁ s₂ : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    traceGe (· ^ σ.n) s₁ s₂ ↔ s₂ ≤ s₁ := by
  constructor
  · -- Forward: traceGe → s₂ ≤ s₁
    -- Specialize the trace at z = s₁: P(s₂, s₁) ≤ P(s₁, s₁)
    -- P(s₁, s₁) = 1/2 (self-comparison), so P(s₂, s₁) ≤ 1/2
    -- This means s₂ⁿ ≤ s₁ⁿ, hence s₂ ≤ s₁ by rpow monotonicity
    intro htrace
    by_contra hlt; push_neg at hlt
    -- hlt : s₁ < s₂, so s₁ⁿ < s₂ⁿ
    have hpow := rpow_lt_rpow (le_of_lt h₁) hlt σ.hn_pos
    -- From trace: pairwiseProb v s₂ s₁ ≤ pairwiseProb v s₁ s₁ for v = (· ^ n)
    have hz := htrace s₁
    simp only [pairwiseProb] at hz
    -- hz : s₂ⁿ / (s₂ⁿ + s₁ⁿ) ≤ s₁ⁿ / (s₁ⁿ + s₁ⁿ)
    have hd₁ : 0 < s₁ ^ σ.n := rpow_pos_of_pos h₁ σ.n
    have hd₂ : 0 < s₂ ^ σ.n := rpow_pos_of_pos h₂ σ.n
    -- From s₁ⁿ < s₂ⁿ: s₂ⁿ/(s₂ⁿ+s₁ⁿ) > 1/2 > s₁ⁿ/(s₁ⁿ+s₁ⁿ) = 1/2
    -- But that contradicts hz
    have : s₁ ^ σ.n / (s₁ ^ σ.n + s₁ ^ σ.n) = 1 / 2 := by
      field_simp; ring
    rw [this] at hz
    have : 1 / 2 < s₂ ^ σ.n / (s₂ ^ σ.n + s₁ ^ σ.n) := by
      rw [lt_div_iff₀ (add_pos hd₂ hd₁)]
      linarith
    linarith
  · -- Backward: s₂ ≤ s₁ → traceGe
    -- s₂ ≤ s₁ → s₂ⁿ ≤ s₁ⁿ → for all z, s₂ⁿ/(s₂ⁿ+zⁿ) ≤ s₁ⁿ/(s₁ⁿ+zⁿ)
    -- Cross-multiplying: s₂ⁿ(s₁ⁿ+zⁿ) ≤ s₁ⁿ(s₂ⁿ+zⁿ), i.e., s₂ⁿ·zⁿ ≤ s₁ⁿ·zⁿ.
    intro hle z
    simp only [pairwiseProb]
    have hpow : s₂ ^ σ.n ≤ s₁ ^ σ.n :=
      rpow_le_rpow (le_of_lt h₂) hle (le_of_lt σ.hn_pos)
    -- TODO: monotonicity of t/(t+c) in t for c ≥ 0, handling z^n ≥ 0
    sorry

-- ============================================================================
-- §4. RSA utility = two-dimensional psychophysics
-- ============================================================================

/-- RSA's multiplicative score factoring is an instance of multidimensional
    psychophysics (§2.C).

    `RSAUtilityDecomposition.score = informativity^α · exp(-α · cost)`

    This is a two-factor product:
    - Factor 1: `informativity^α` — a Stevens power law with exponent `α`
    - Factor 2: `exp(-α · cost)` — a Fechner exponential with rate `-α`

    The multiplicative independence axiom from §2.C says that the relative
    contribution of informativity to choice probability is independent of
    cost, and vice versa. This is a substantive empirical prediction of RSA,
    not a modeling convenience — it says speakers' sensitivity to informativity
    doesn't depend on utterance cost. -/
theorem rsa_is_two_dimensional_psychophysics (d : RSAUtilityDecomposition) :
    d.score = d.informativity ^ d.α * Real.exp (-d.α * d.cost) := by
  rfl

/-- The RSA informativity factor is a Stevens power law.

    `informativity^α = StevensScale.psi ⟨α, 1,...⟩ informativity`
    (with coefficient `k = 1`). -/
theorem rsa_informativity_is_stevens (d : RSAUtilityDecomposition)
    (hα_pos : 0 < d.α) :
    d.informativity ^ d.α =
    (StevensScale.mk d.α 1 hα_pos one_pos).psi d.informativity := by
  simp only [StevensScale.psi, one_mul]

/-- The full RSA decomposition is a two-dimensional psychophysical scale:
    log(score) = α · log(informativity) + (-α) · cost.

    In log-space, each dimension contributes additively with its own
    "exponent" (α for informativity, -α for cost). This additive structure
    in log-space is exactly Luce's Chapter 3 decomposition viewed through
    the Stevens-Fechner equivalence. -/
theorem rsa_log_decomposition (d : RSAUtilityDecomposition)
    (hinfo_pos : 0 < d.informativity) :
    Real.log d.score = d.α * Real.log d.informativity + (-d.α) * d.cost := by
  have := rsa_utility_decomposition d hinfo_pos
  linarith

end Core
