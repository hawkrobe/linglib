/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.KullbackLeibler.Basic
public import Linglib.Core.Probability.ConditionalProbability
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Kullback-Leibler divergence of conditional measures

The conditioning identity: for a probability measure `μ` and an event `s` of nonzero mass,
`klDiv (μ[|s]) μ = −log μ(s)`, so Bayesian update by pure restriction costs exactly the
information content of the event. More generally the divergence between two conditionings of one
finite measure is the log of the ratio of the events' masses when the first event is almost
contained in the second (`klDiv_cond_cond`), and infinite otherwise
(`klDiv_cond_cond_eq_top_iff`). A point mass is a probability measure conditioned on the point,
so its divergence from the measure is the surprisal of the point (`coe_klDiv_dirac_left`).

`[UPSTREAM]` candidate for `Mathlib/InformationTheory/KullbackLeibler/`
(placement and namespace mirror `ChainRule.lean`, the directory's other
file combining `klDiv` with probability constructions).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace InformationTheory

/-- The Kullback-Leibler divergence of the conditional measure `μ[|s]` from
`μ` is the information content of the event: `−log μ(s)`. The core of
[levy-2008]'s equivalence of relative-entropy difficulty and surprisal. -/
theorem klDiv_cond_self {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {s : Set Ω} (hs : MeasurableSet s) (hs0 : μ s ≠ 0) :
    klDiv (μ[|s]) μ = ENNReal.ofReal (-Real.log (μ s).toReal) := by
  have := cond_isProbabilityMeasure (μ := μ) hs0
  rw [klDiv_of_rnDeriv_ae_const cond_absolutelyContinuous (rnDeriv_cond_ae_const hs),
    ENNReal.toReal_inv, Real.log_inv]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {s t : Set Ω}

/-- The divergence between two conditionings of one measure, the first on an event almost
contained in the second, is the log of the ratio of the events' masses. -/
theorem klDiv_cond_cond (hs : MeasurableSet s) (ht : MeasurableSet t) (hs0 : μ s ≠ 0)
    (hst : s ≤ᵐ[μ] t) :
    klDiv μ[|s] μ[|t] = ENNReal.ofReal (Real.log (μ.real t / μ.real s)) := by
  have hts : μ[|t] s = (μ t)⁻¹ * μ s := by
    rw [cond_apply ht, Set.inter_comm, measure_congr (Filter.inter_eventuallyEqSet_left.2 hst)]
  have := cond_isProbabilityMeasure (μ := μ) fun h ↦ hs0 (measure_mono_null_ae hst h)
  rw [← cond_cond_of_ae_le hs ht hst, klDiv_cond_self _ hs (hts ▸ mul_ne_zero
    (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) hs0), hts, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← Real.log_inv, mul_inv, inv_inv, measureReal_def, measureReal_def,
    div_eq_mul_inv]

/-- Among the events almost containing `s`, the one of smaller mass has its conditional closer
to `μ[|s]`. -/
theorem klDiv_cond_cond_lt_iff {t' : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (ht' : MeasurableSet t') (hs0 : μ s ≠ 0) (hst : s ≤ᵐ[μ] t) (hst' : s ≤ᵐ[μ] t') :
    klDiv μ[|s] μ[|t] < klDiv μ[|s] μ[|t'] ↔ μ t < μ t' := by
  have hpos : 0 < μ.real s := ENNReal.toReal_pos hs0 (measure_ne_top _ _)
  have hle {v : Set Ω} (hv : s ≤ᵐ[μ] v) : μ.real s ≤ μ.real v :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hv)
  rw [klDiv_cond_cond hs ht hs0 hst, klDiv_cond_cond hs ht' hs0 hst',
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.log_nonneg ((one_le_div hpos).2 (hle hst))),
    Real.log_lt_log_iff (div_pos (hpos.trans_le (hle hst)) hpos)
      (div_pos (hpos.trans_le (hle hst')) hpos),
    div_lt_div_iff_of_pos_right hpos, measureReal_def, measureReal_def,
    ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)]

/-- The divergence between two conditionings of one measure is infinite exactly when the first
event is not almost contained in the second. -/
theorem klDiv_cond_cond_eq_top_iff (hs : MeasurableSet s) (ht : MeasurableSet t) :
    klDiv μ[|s] μ[|t] = ∞ ↔ ¬ s ≤ᵐ[μ] t := by
  refine ⟨fun h hst ↦ ?_, fun h ↦
    klDiv_of_not_ac fun hac ↦ h ((cond_absolutelyContinuous_cond_iff hs ht).1 hac)⟩
  rcases eq_or_ne (μ s) 0 with hs0 | hs0
  · rw [cond_eq_zero_of_meas_eq_zero hs0, klDiv_zero_left] at h
    exact measure_ne_top _ _ h
  · rw [klDiv_cond_cond hs ht hs0 hst] at h
    exact ENNReal.ofReal_ne_top h

/-- The divergence of a probability measure from a point mass is the surprisal of the point. -/
theorem coe_klDiv_dirac_left [MeasurableSingletonClass Ω] (a : Ω) (ν : Measure Ω)
    [IsZeroOrProbabilityMeasure ν] : (klDiv (Measure.dirac a) ν : EReal) = -ENNReal.log (ν {a}) := by
  rcases eq_or_ne (ν {a}) 0 with h0 | h0
  · rw [klDiv_of_not_ac fun h ↦ by simpa using h h0, h0, ENNReal.log_zero, EReal.neg_bot,
      EReal.coe_ennreal_top]
  · have : NeZero ν := ⟨fun h ↦ h0 (by rw [h]; rfl)⟩
    have := (eq_zero_or_isProbabilityMeasure ν).resolve_left (NeZero.ne ν)
    have hd : ν[|{a}] = Measure.dirac a := by
      rw [ProbabilityTheory.cond, Measure.restrict_singleton, smul_smul,
        ENNReal.inv_mul_cancel h0 (measure_ne_top _ _), one_smul]
    rw [← hd, klDiv_cond_self ν (.singleton a) h0, EReal.coe_ennreal_ofReal,
      max_eq_left (neg_nonneg.2 (Real.log_nonpos ENNReal.toReal_nonneg
        (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)))),
      ENNReal.log_pos_real h0 (measure_ne_top _ _), EReal.coe_neg]

end InformationTheory
