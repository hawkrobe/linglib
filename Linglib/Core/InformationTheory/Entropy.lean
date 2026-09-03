/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.InformationTheory.KullbackLeibler.Finite
import Linglib.Core.InformationTheory.MutualInformation
import Linglib.Core.MeasureTheory.Measure.Prod
import Linglib.Core.Probability.UniformOn
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Entropy of a measure

The Shannon entropy of a measure on a measurable space, following the PFR project's
`ForMathlib` entropy: `Hm[μ] = ∑' s, negMulLog (((μ univ)⁻¹ • μ).real {s})`, normalized so
that a finite measure has the entropy of its probability normalization. Mutual information is
the entropy difference `Im[μ] = Hm[μ.fst] + Hm[μ.snd] - Hm[μ]`; on a finite type it is the
real part of the Kullback–Leibler form `mutualInfo`, hence nonnegative.

## Main definitions

* `measureEntropy`, notation `Hm[μ]`
* `measureMutualInfo`, notation `Im[μ]`

## Main results

* `measureEntropy_le_log_card`: entropy is at most the log of the cardinality;
  `measureEntropy_uniformOn`: the uniform measure attains it.
* `measureMutualInfo_eq_toReal_mutualInfo`, `measureMutualInfo_nonneg`.

## References

* [cover-thomas-2006], chapter 2.
* The PFR project, `PFR/ForMathlib/Entropy/Measure.lean`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

section measureEntropy

variable {μ : Measure S}

/-- Entropy of a measure. The measure is normalized by `(μ Set.univ)⁻¹`, so that a finite
measure has the entropy of its probability normalization and every other measure has entropy
`0`; on a probability measure `simp` removes the normalization. -/
noncomputable def measureEntropy (μ : Measure S) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})

@[inherit_doc measureEntropy] scoped notation:100 "Hm[" μ "]" => measureEntropy μ

@[simp] theorem measureEntropy_zero : Hm[(0 : Measure S)] = 0 := by simp [measureEntropy]

theorem measureEntropy_of_not_isFiniteMeasure (h : ¬ IsFiniteMeasure μ) : Hm[μ] = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]

theorem measureEntropy_of_isProbabilityMeasure (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, negMulLog (μ.real {s}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | _ <;> simp [measureEntropy]

theorem measureEntropy_eq_sum [Fintype S] (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑ s, negMulLog (μ.real {s}) := by
  rw [measureEntropy_of_isProbabilityMeasure, tsum_fintype]

theorem measureEntropy_univ_smul : Hm[(μ Set.univ)⁻¹ • μ] = Hm[μ] := by
  by_cases hμ : IsFiniteMeasure μ
  · rcases eq_zero_or_neZero μ with rfl | _
    · simp
    · simp [measureEntropy]
  · rw [measureEntropy_of_not_isFiniteMeasure hμ]
    rw [not_isFiniteMeasure_iff] at hμ
    simp [hμ]

theorem measureEntropy_nonneg (μ : Measure S) : 0 ≤ Hm[μ] := by
  by_cases hμ : IsFiniteMeasure μ
  · refine tsum_nonneg fun s => negMulLog_nonneg (by positivity) ?_
    rcases eq_zero_or_neZero μ with rfl | _
    · simp
    · exact measureReal_le_one
  · rw [measureEntropy_of_not_isFiniteMeasure hμ]

variable [MeasurableSingletonClass S]

@[simp] theorem measureEntropy_dirac (x : S) : Hm[Measure.dirac x] = 0 := by
  rw [measureEntropy_of_isProbabilityMeasure, tsum_eq_single x]
  · simp [measureReal_def]
  · intro y hy
    simp [measureReal_def, hy.symm]

private theorem measureEntropy_le_log_card_of_isProbabilityMeasure [Fintype S] (μ : Measure S)
    [IsProbabilityMeasure μ] : Hm[μ] ≤ log (Fintype.card S) := by
  have : Nonempty S := μ.nonempty_of_neZero
  set N := Fintype.card S
  have hN : (N : ℝ) ≠ 0 := by positivity
  rw [measureEntropy_eq_sum]
  calc ∑ s, negMulLog (μ.real {s}) = N * ∑ s, (N : ℝ)⁻¹ * negMulLog (μ.real {s}) := by
        rw [Finset.mul_sum]
        congr with s
        rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
    _ ≤ N * negMulLog (∑ s, (N : ℝ)⁻¹ * μ.real {s}) := by
        gcongr
        exact concaveOn_negMulLog.le_map_sum (by simp) (by simp [N]) (by simp)
    _ = N * negMulLog (N : ℝ)⁻¹ := by
        rw [← Finset.mul_sum, sum_measureReal_singleton, Finset.coe_univ, probReal_univ, mul_one]
    _ = log N := by simp [negMulLog, ← mul_assoc, mul_inv_cancel₀ hN]

/-- Entropy is at most the logarithm of the cardinality of the type. -/
theorem measureEntropy_le_log_card [Fintype S] (μ : Measure S) :
    Hm[μ] ≤ log (Fintype.card S) := by
  by_cases hμ : IsFiniteMeasure μ
  · rcases eq_zero_or_neZero μ with rfl | _
    · simpa using log_natCast_nonneg (Fintype.card S)
    · rw [← measureEntropy_univ_smul]
      exact measureEntropy_le_log_card_of_isProbabilityMeasure _
  · rw [measureEntropy_of_not_isFiniteMeasure hμ]
    exact log_natCast_nonneg _

/-- The entropy of the uniform measure on a finite set is the logarithm of its cardinality. -/
theorem measureEntropy_uniformOn [Fintype S] [DecidableEq S] {A : Finset S} (hA : A.Nonempty) :
    Hm[uniformOn (A : Set S)] = log A.card := by
  have := isProbabilityMeasure_uniformOn A.finite_toSet (by simpa using hA)
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  rw [measureEntropy_eq_sum]
  simp_rw [measureReal_def, uniformOn_finset_apply_singleton, apply_ite ENNReal.toReal,
    apply_ite negMulLog, ENNReal.toReal_zero, negMulLog_zero, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    negMulLog, log_inv]
  field_simp

end measureEntropy

section measureMutualInfo

/-- Mutual information of a measure on a product: the entropies of the marginals less the
entropy of the joint. -/
noncomputable def measureMutualInfo (μ : Measure (S × T)) : ℝ :=
  Hm[μ.fst] + Hm[μ.snd] - Hm[μ]

@[inherit_doc measureMutualInfo] scoped notation:100 "Im[" μ "]" => measureMutualInfo μ

variable [Fintype S] [Fintype T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  (μ : Measure (S × T)) [IsProbabilityMeasure μ]

/-- On a finite product, the entropy form of mutual information is the real part of the
Kullback–Leibler form. -/
theorem measureMutualInfo_eq_toReal_mutualInfo : Im[μ] = (mutualInfo μ).toReal := by
  have h (a : S) (b : T) :
      μ.real {(a, b)} * log (μ.real {(a, b)} / (μ.fst.prod μ.snd).real {(a, b)})
        = -negMulLog (μ.real {(a, b)}) - μ.real {(a, b)} * log (μ.fst.real {a})
          - μ.real {(a, b)} * log (μ.snd.real {b}) := by
    rw [Measure.prod_real_singleton]
    obtain hp | hp := eq_or_ne (μ.real {(a, b)}) 0
    · simp [hp]
    · have hpos : 0 < μ.real {(a, b)} := lt_of_le_of_ne measureReal_nonneg hp.symm
      have ha : μ.real {(a, b)} ≤ μ.fst.real {a} := by
        rw [Measure.fst_real_singleton_eq_sum]
        exact Finset.single_le_sum (f := fun b => μ.real {(a, b)}) (fun _ _ => measureReal_nonneg)
          (Finset.mem_univ b)
      have hb : μ.real {(a, b)} ≤ μ.snd.real {b} := by
        rw [Measure.snd_real_singleton_eq_sum]
        exact Finset.single_le_sum (f := fun a => μ.real {(a, b)}) (fun _ _ => measureReal_nonneg)
          (Finset.mem_univ a)
      rw [log_div hp (mul_ne_zero (hpos.trans_le ha).ne' (hpos.trans_le hb).ne'),
        log_mul (hpos.trans_le ha).ne' (hpos.trans_le hb).ne', negMulLog]
      ring
  have h1 : ∑ a, ∑ b, μ.real {(a, b)} * log (μ.fst.real {a})
      = ∑ a, μ.fst.real {a} * log (μ.fst.real {a}) := by
    simp_rw [← Finset.sum_mul, ← Measure.fst_real_singleton_eq_sum]
  have h2 : ∑ a, ∑ b, μ.real {(a, b)} * log (μ.snd.real {b})
      = ∑ b, μ.snd.real {b} * log (μ.snd.real {b}) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Measure.snd_real_singleton_eq_sum]
  rw [mutualInfo, toReal_klDiv_eq_sum_log_div μ.absolutelyContinuous_fst_prod_snd,
    measureMutualInfo, measureEntropy_eq_sum, measureEntropy_eq_sum, measureEntropy_eq_sum]
  simp_rw [Fintype.sum_prod_type, h, Finset.sum_sub_distrib, Finset.sum_neg_distrib, h1, h2,
    negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

theorem measureMutualInfo_nonneg : 0 ≤ Im[μ] := by
  rw [measureMutualInfo_eq_toReal_mutualInfo]
  exact ENNReal.toReal_nonneg

end measureMutualInfo

end InformationTheory
