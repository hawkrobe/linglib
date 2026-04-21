import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Linglib.Core.Causal.SEM.Counterfactual

/-!
# Causal Strength Models
@cite{icard-et-al-2017}

Theory-layer definitions for **causal strength**: computational models
that rank candidate causes by importance, given a causal model.

Two models are formalized:

1. **Necessity-Sufficiency Model** (NSM, @cite{icard-et-al-2017}):
   `NSM(C) = P(C) · Suf(C) + (1 − P(C)) · Nec(C)`

2. **Sampling propensity** (shared by NSM and CESM):
   `SP(V) = s · ⟦V⟧^w@ + (1 − s) · P(V)`

These definitions are theory-layer infrastructure imported by study files
(e.g., `KonukEtAl2026`, `BellerGerstenberg2025`).
-/

namespace Semantics.Causation.Strength

/-! ## Sampling Propensity

The probability that a variable retains its actual-world value in a
counterfactual sample. Interpolates between the actual value (stability
parameter s) and the prior probability (1 − s). -/

/-- Sampling propensity of a binary variable V.

- `s`: stability parameter ∈ [0,1] — probability of copying the actual value
- `actualValue`: ⟦V⟧^w@ ∈ {0,1} — the variable's value in the actual world
- `priorProb`: P(V) — the prior probability of V being true -/
def samplingPropensity (s actualValue priorProb : ℚ) : ℚ :=
  s * actualValue + (1 - s) * priorProb

/-- At s = 0, sampling propensity reduces to the prior. -/
theorem sp_at_zero (v p : ℚ) : samplingPropensity 0 v p = p := by
  simp [samplingPropensity]

/-- At s = 1, sampling propensity reduces to the actual value. -/
theorem sp_at_one (v p : ℚ) : samplingPropensity 1 v p = v := by
  simp [samplingPropensity]

/-! ## Necessity-Sufficiency Model (NSM)

The causal strength of a candidate cause C for outcome E, computed as a
weighted combination of sufficiency and necessity scores. -/

/-- NSM formula: `NSM(C) = P(C) · Suf(C) + (1 − P(C)) · Nec(C)`.

- `pC`: prior probability (or sampling propensity) of the cause
- `suf`: sufficiency score ∈ [0,1]
- `nec`: necessity score ∈ [0,1] -/
def nsm (pC suf nec : ℚ) : ℚ := pC * suf + (1 - pC) * nec

/-- When Suf = 1, NSM simplifies to P(C) + (1 − P(C)) · Nec. -/
theorem nsm_suf_one (pC nec : ℚ) : nsm pC 1 nec = pC + (1 - pC) * nec := by
  simp [nsm]

/-- Sufficient and necessary: NSM = 1 regardless of probability. -/
theorem nsm_suf_nec (pC : ℚ) : nsm pC 1 1 = 1 := by simp [nsm]

/-- Sufficient but not necessary: NSM = P(C). -/
theorem nsm_suf_only (pC : ℚ) : nsm pC 1 0 = pC := by simp [nsm]

/-- Necessary but not sufficient: NSM = 1 − P(C). -/
theorem nsm_nec_only (pC : ℚ) : nsm pC 0 1 = 1 - pC := by simp [nsm]

/-- Neither sufficient nor necessary: NSM = 0. -/
theorem nsm_neither (pC : ℚ) : nsm pC 0 0 = 0 := by simp [nsm]

/-- NSM is monotone in sufficiency. -/
theorem nsm_mono_suf (pC nec : ℚ) (hpC : 0 ≤ pC) (s₁ s₂ : ℚ) (h : s₁ ≤ s₂) :
    nsm pC s₁ nec ≤ nsm pC s₂ nec := by
  unfold nsm; linarith [mul_le_mul_of_nonneg_left h hpC]

end Semantics.Causation.Strength
