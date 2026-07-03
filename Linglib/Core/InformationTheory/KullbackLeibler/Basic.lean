/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Kullback-Leibler divergence: probability-measure forms

Extensions to mathlib's `InformationTheory/KullbackLeibler/Basic.lean`, its
`[UPSTREAM]` home. For probability measures the finite-measure correction term
in `klDiv` cancels, giving the textbook integral form; a distribution whose
density is a.e. constant has KL divergence `log c`.
-/

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}

/-- For probability measures, `klDiv` is the integral of the log-likelihood
    ratio: the finite-measure correction term cancels. -/
theorem klDiv_eq_ofReal_integral_llr [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) (hint : Integrable (llr μ ν) μ) :
    klDiv μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ) := by
  rw [klDiv_of_ac_of_integrable hμν hint]
  simp [measureReal_def]

/-- A distribution whose log-likelihood ratio to `ν` is a.e. the constant `r`
    has KL divergence `r` from it. -/
theorem klDiv_of_llr_ae_const [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) {r : ℝ} (h : llr μ ν =ᵐ[μ] fun _ => r) :
    klDiv μ ν = ENNReal.ofReal r := by
  have hint : Integrable (llr μ ν) μ := (integrable_const _).congr h.symm
  rw [klDiv_eq_ofReal_integral_llr hμν hint, integral_congr_ae h, integral_const]
  simp [measureReal_def]

/-- A distribution whose density with respect to `ν` is a.e. the constant `c`
    has KL divergence `log c` from it. -/
theorem klDiv_of_rnDeriv_ae_const [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) {c : ℝ≥0∞}
    (h : μ.rnDeriv ν =ᵐ[μ] fun _ => c) :
    klDiv μ ν = ENNReal.ofReal (Real.log c.toReal) :=
  klDiv_of_llr_ae_const hμν <| h.mono fun _ hx => by rw [llr, hx]

end InformationTheory
