import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Basic

/-!
# Gibbs Variational Principle (Re-export)

This file re-exports Gibbs variational and Bayesian optimality results from
`Core.RationalAction`, where they now live. The RSA-specific forms
(`speaker_optimal_per_meaning`, `listener_optimal_per_utterance`) are
thin wrappers around the generic theorems.
-/

namespace RSA.GibbsVariational

open Real Finset Core

variable {ι : Type*} [Fintype ι]

-- Re-export KL divergence
noncomputable abbrev klFinite (p q : ι → ℝ) : ℝ := Core.klFinite p q

-- Re-export speaker objective
noncomputable abbrev speakerObj (v : ι → ℝ) (α : ℝ) (s : ι → ℝ) : ℝ := Core.speakerObj v α s

theorem kl_finite_nonneg (p q : ι → ℝ) (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = ∑ i, q i) :
    0 ≤ klFinite p q :=
  Core.kl_nonneg p q hq hp hsum

-- RSA-Specific Forms

private theorem speakerObj_eq_sum (v : ι → ℝ) (α : ℝ) (f : ι → ℝ) :
    ∑ u, (negMulLog (f u) + α * f u * v u) =
    (∑ u, negMulLog (f u)) + α * ∑ u, f u * v u := by
  have : ∑ u, (negMulLog (f u) + α * f u * v u) =
      ∑ u, negMulLog (f u) + ∑ u, α * (f u * v u) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [this, ← Finset.mul_sum]

theorem speaker_optimal_per_meaning [Nonempty ι] (v : ι → ℝ) (α : ℝ)
    (s : ι → ℝ) (hs_nonneg : ∀ i, 0 ≤ s i) (hs_sum : ∑ i, s i = 1) :
    ∑ u, (negMulLog (s u) + α * s u * v u) ≤
    ∑ u, (negMulLog (Core.softmax v α u) + α * Core.softmax v α u * v u) := by
  rw [speakerObj_eq_sum, speakerObj_eq_sum]
  exact Core.gibbs_variational v α s hs_nonneg hs_sum

theorem gibbs_maximizes [Nonempty ι] (v : ι → ℝ) (α : ℝ)
    (s : ι → ℝ) (hs_nonneg : ∀ i, 0 ≤ s i) (hs_sum : ∑ i, s i = 1) :
    speakerObj v α s ≤ speakerObj v α (Core.softmax v α) :=
  speaker_optimal_per_meaning v α s hs_nonneg hs_sum

theorem bayesian_maximizes [Nonempty ι] (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hC_pos : 0 < ∑ i, w i)
    (L : ι → ℝ) (hL_pos : ∀ i, 0 < L i) (hL_sum : ∑ i, L i = 1) :
    ∑ i, w i * log (L i) ≤ ∑ i, w i * log (w i / ∑ j, w j) :=
  Core.bayesian_maximizes w hw_nonneg hC_pos L hL_pos hL_sum

theorem listener_optimal_per_utterance [Nonempty ι] (w : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hC_pos : 0 < ∑ i, w i)
    (L : ι → ℝ) (hL_pos : ∀ i, 0 < L i) (hL_sum : ∑ i, L i = 1) :
    ∑ i, w i * log (L i) ≤ ∑ i, w i * log (w i / ∑ j, w j) :=
  Core.bayesian_maximizes w hw_nonneg hC_pos L hL_pos hL_sum

end RSA.GibbsVariational
