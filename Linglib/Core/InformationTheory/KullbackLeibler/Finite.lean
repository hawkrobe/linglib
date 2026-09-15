/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.InformationTheory.KullbackLeibler.Basic
import Linglib.Core.MeasureTheory.Measure.Decomposition.RadonNikodym
import Linglib.Core.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Kullback–Leibler divergence on a finite type

On a finite type with measurable singletons the Radon–Nikodym derivative is the ratio of atom
masses, so `klDiv` is a finite sum, and for probability measures its real part is the textbook
relative entropy `∑ a, μ {a} * log (μ {a} / ν {a})` ([cover-thomas-2006], chapter 2).
`[UPSTREAM]` candidate for `Mathlib/InformationTheory/KullbackLeibler/`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
  {μ ν : Measure α}

/-- On a finite type the log-likelihood ratio is integrable, so the divergence is infinite exactly
when the first measure is not absolutely continuous with respect to the second. -/
theorem klDiv_eq_top_iff_not_ac [IsFiniteMeasure μ] : klDiv μ ν = ∞ ↔ ¬ μ ≪ ν := by
  rw [klDiv_eq_top_iff]
  exact ⟨λ h hμν => h hμν .of_finite, λ h hμν => absurd hμν h⟩

theorem klDiv_eq_sum_klFun [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    klDiv μ ν = ∑ a, ν {a} * ENNReal.ofReal (klFun (μ {a} / ν {a}).toReal) := by
  have h : (fun a => ENNReal.ofReal (klFun (μ.rnDeriv ν a).toReal))
      =ᵐ[ν] fun a => ENNReal.ofReal (klFun (μ {a} / ν {a}).toReal) := by
    filter_upwards [Measure.rnDeriv_eq_div_singleton hμν] with a ha
    rw [ha]
  rw [klDiv_eq_lintegral_klFun_of_ac hμν, lintegral_congr_ae h, lintegral_fintype]
  simp_rw [mul_comm]

theorem toReal_klDiv_eq_sum_log_div [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal = ∑ a, μ.real {a} * log (μ.real {a} / ν.real {a}) := by
  have key (a : α) : ν.real {a} * klFun (μ.real {a} / ν.real {a})
      = μ.real {a} * log (μ.real {a} / ν.real {a}) + (ν.real {a} - μ.real {a}) := by
    obtain hq | hq := eq_or_ne (ν.real {a}) 0
    · have hp : μ.real {a} = 0 := by
        rw [measureReal_eq_zero_iff (measure_ne_top _ _)] at hq ⊢
        exact hμν hq
      simp [hp, hq]
    · unfold klFun; field_simp; ring
  have h : (fun a => klFun (μ.rnDeriv ν a).toReal)
      =ᵐ[ν] fun a => klFun (μ {a} / ν {a}).toReal := by
    filter_upwards [Measure.rnDeriv_eq_div_singleton hμν] with a ha
    rw [ha]
  rw [toReal_klDiv_eq_integral_klFun hμν, integral_congr_ae h, integral_fintype .of_finite]
  simp_rw [smul_eq_mul, ENNReal.toReal_div, ← measureReal_def, key,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_measureReal_singleton,
    Finset.coe_univ, probReal_univ, sub_self, add_zero]

/-- The divergence from the uniform measure on a nonempty finset to the uniform measure on a
superset is the log of the ratio of their sizes. -/
theorem klDiv_uniformOn_of_subset [DecidableEq α] {A B : Finset α} (hA : A.Nonempty)
    (hAB : A ⊆ B) :
    klDiv (uniformOn (A : Set α)) (uniformOn (B : Set α)) =
      ENNReal.ofReal (log (B.card / A.card)) := by
  have hac := uniformOn_absolutelyContinuous_of_subset B.finite_toSet (Finset.coe_subset.2 hAB)
  have := isProbabilityMeasure_uniformOn A.finite_toSet (Finset.coe_nonempty.2 hA)
  have := isProbabilityMeasure_uniformOn B.finite_toSet (Finset.coe_nonempty.2 (hA.mono hAB))
  rw [klDiv_of_rnDeriv_ae_const hac (c := (B.card : ℝ≥0∞) / A.card), ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  filter_upwards [(Measure.rnDeriv_eq_div_singleton hac).filter_mono hac.ae_le,
    ae_cond_mem (A.finite_toSet.measurableSet)] with a ha hmem
  rw [ha, uniformOn_finset_apply_singleton, uniformOn_finset_apply_singleton,
    ite_eq_left (Finset.mem_coe.1 hmem), ite_eq_left (hAB (Finset.mem_coe.1 hmem)), div_eq_mul_inv,
    inv_inv, mul_comm, ← div_eq_mul_inv]

end InformationTheory
