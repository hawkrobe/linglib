/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Conditional measures: extensions

Measure-level facts about `ProbabilityTheory.cond` beyond mathlib's
`Mathlib/Probability/ConditionalProbability.lean`. `[UPSTREAM]` candidates.

## Main results

* `ProbabilityTheory.klDiv_cond_self` — the conditioning identity: the KL
  divergence of `μ[|s]` from `μ` is the information content of the event,
  `−log μ(s)`.
-/

namespace ProbabilityTheory

open scoped ProbabilityTheory

/-- **Conditioning identity** (measure level): for a probability measure `μ`,
    the KL divergence of the conditional measure `μ[|s]` from `μ` is the
    information content of the event: `−log μ(s)`. The general core of
    [levy-2008]\'s equivalence of relative-entropy difficulty and surprisal.
    `[UPSTREAM]` candidate: mathlib has `klDiv` and `Measure.cond` but no
    conditioning identity. -/
theorem klDiv_cond_self {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    {s : Set Ω} (hs : MeasurableSet s) (hs0 : μ s ≠ 0) :
    InformationTheory.klDiv (μ[|s]) μ = ENNReal.ofReal (-Real.log (μ s).toReal) := by
  have : MeasureTheory.IsProbabilityMeasure (μ[|s]) :=
    cond_isProbabilityMeasure hs0
  -- The density of `μ[|s]` with respect to `μ` is `(μ s)⁻¹`, `μ[|s]`-a.e.
  have hrn : (μ[|s]).rnDeriv μ =ᵐ[μ] s.indicator fun _ => (μ s)⁻¹ := by
    have h1 : ((μ s)⁻¹ • μ.restrict s).rnDeriv μ
        =ᵐ[μ] (μ s)⁻¹ • (μ.restrict s).rnDeriv μ :=
      MeasureTheory.Measure.rnDeriv_smul_left_of_ne_top' _ _
        (ENNReal.inv_ne_top.mpr hs0)
    refine h1.trans ((MeasureTheory.Measure.rnDeriv_restrict_self μ hs).mono
      fun x hx => ?_)
    rw [Pi.smul_apply, hx]
    by_cases hxs : x ∈ s <;> simp [hxs]
  have hae : ∀ᵐ x ∂(μ[|s]), x ∈ s := by
    rw [MeasureTheory.ae_iff]
    show μ[|s] sᶜ = 0
    rw [cond_apply hs, Set.inter_compl_self, MeasureTheory.measure_empty,
      mul_zero]
  have hllr : MeasureTheory.llr (μ[|s]) μ
      =ᵐ[μ[|s]] fun _ => -Real.log (μ s).toReal := by
    filter_upwards [cond_absolutelyContinuous.ae_eq hrn, hae]
      with x hx hxs
    rw [MeasureTheory.llr, hx, Set.indicator_of_mem hxs, ENNReal.toReal_inv,
      Real.log_inv]
  have hint : MeasureTheory.Integrable (MeasureTheory.llr (μ[|s]) μ) (μ[|s]) :=
    (MeasureTheory.integrable_const _).congr hllr.symm
  rw [InformationTheory.klDiv_of_ac_of_integrable
      cond_absolutelyContinuous hint,
    MeasureTheory.integral_congr_ae hllr, MeasureTheory.integral_const]
  simp [MeasureTheory.measureReal_def]

end ProbabilityTheory
