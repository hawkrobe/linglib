module

public import Linglib.Core.InformationTheory.Entropy
public import Linglib.Core.InformationTheory.KullbackLeibler.Cond
public import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
public import Linglib.Pragmatics.RSA.Basic

/-!
# Speakers with beliefs

A speaker who does not know the state believes a measure on states. `RSA.speaker` scores an
utterance by the expected log-probability its listener gives the state under that belief, as
Goodman and Stuhlmüller do. This file relates that score to the Kullback–Leibler divergence of the
listener's posterior from the belief: the two differ by the entropy of the belief, which no
utterance changes, so they define the same speaker. An utterance whose listener rules out a state
the speaker entertains is never produced.

## Main results

* `RSA.speaker_apply_singleton_eq_zero_iff`: the speaker produces exactly the utterances whose
  listener rules out no state she entertains.
* `RSA.speaker_eq_speakerOfScore_sum_log`: the speaker is the softmax of the expected
  log-probability the listener gives the state under her belief.
* `RSA.speaker_eq_speakerOfScore_klDiv`: the speaker is the softmax of the negative divergence of
  the listener from her belief.
* `RSA.speaker_zero_cond_literalListener_real_singleton_lt_iff`: a speaker whose belief is the
  prior conditioned on what she knows prefers, among the utterances her knowledge entails, the
  one of smaller prior mass.

## References

* [goodman-stuhlmuller-2013]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace RSA

variable {W U O : Type*} [MeasurableSpace W] [Fintype W] {α : ℝ} {C : U → ℝ}
  {L : U → Measure W} {b : O → Measure W} {o : O} {u u' : U}

/-- Under domination the product of powers is the exponential of the expected log-probability. -/
private theorem prod_rpow_eq_ofReal_exp {β ν : Measure W} [IsFiniteMeasure β] [IsFiniteMeasure ν]
    (h : β ≪ ν) (α : ℝ) :
    ∏ w, ν {w} ^ (α * β.real {w}) =
      ENNReal.ofReal (Real.exp (α * ∑ w, β.real {w} * Real.log (ν.real {w}))) := by
  rw [Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rcases eq_or_ne (β.real {w}) 0 with h0 | h0
  · simp [h0]
  · have hν : ν {w} ≠ 0 := fun hν ↦ h0 (by rw [measureReal_def, h hν, ENNReal.toReal_zero])
    have hpos : 0 < ν.real {w} := ENNReal.toReal_pos hν (measure_ne_top _ _)
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν {w}), ← measureReal_def,
      ENNReal.ofReal_rpow_of_pos hpos, Real.rpow_def_of_pos hpos]
    congr 2
    ring

variable [MeasurableSpace U] [Fintype U] [MeasurableSpace O] [Countable O]
  [MeasurableSingletonClass O]

/-- When every listener dominates every belief, the speaker is the softmax of the expected
log-probability the listener gives the state under the belief, less the cost. -/
theorem speaker_eq_speakerOfScore_sum_log [∀ o, IsFiniteMeasure (b o)]
    [∀ u, IsFiniteMeasure (L u)] (h : ∀ o u, b o ≪ L u) :
    speaker α C L b = speakerOfScore fun o u ↦
      ((α * (∑ w, (b o).real {w} * Real.log ((L u).real {w}) - C u) : ℝ) : EReal) := by
  refine congrArg Kernel.ofWeights (funext fun o ↦ funext fun u ↦ ?_)
  rw [prod_rpow_eq_ofReal_exp (h o u), EReal.exp_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 2
  ring

variable [MeasurableSingletonClass U]

/-- The speaker never produces an utterance whose listener rules out a state she entertains. -/
theorem speaker_apply_singleton_eq_zero_iff [IsFiniteMeasure (b o)] [∀ u, IsFiniteMeasure (L u)]
    (hα : 0 < α) : speaker α C L b o {u} = 0 ↔ ∃ w, b o {w} ≠ 0 ∧ L u {w} = 0 := by
  have hw (v : U) : (∏ w, L v {w} ^ (α * (b o).real {w})) *
      ENNReal.ofReal (Real.exp (-(α * C v))) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ ↦ ENNReal.rpow_ne_top_of_nonneg
      (mul_nonneg hα.le measureReal_nonneg) (measure_ne_top _ _)) ENNReal.ofReal_ne_top
  rw [speaker_apply_singleton, ENNReal.div_eq_zero_iff,
    or_iff_left (ENNReal.sum_ne_top.2 fun v _ ↦ hw v), mul_eq_zero,
    or_iff_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne', Finset.prod_eq_zero_iff]
  refine exists_congr fun w ↦ ?_
  rw [ENNReal.rpow_eq_zero_iff, or_iff_left fun h ↦ measure_ne_top _ _ h.1,
    mul_pos_iff_of_pos_left hα, measureReal_def,
    ENNReal.toReal_pos_iff, and_iff_left (measure_lt_top _ _), pos_iff_ne_zero]
  simp [and_comm]

theorem speaker_apply_singleton_eq_zero_iff_not_ac [IsFiniteMeasure (b o)]
    [∀ u, IsFiniteMeasure (L u)] (hα : 0 < α) : speaker α C L b o {u} = 0 ↔ ¬ b o ≪ L u := by
  rw [speaker_apply_singleton_eq_zero_iff hα, Measure.absolutelyContinuous_iff_forall_singleton,
    not_forall]
  exact exists_congr fun w ↦ by rw [Classical.not_imp, and_comm]

variable [MeasurableSingletonClass W]

/-- The product of powers is the exponential of the negative divergence, up to a factor fixed by
the entropy of the belief. -/
private theorem prod_rpow_eq_exp_klDiv {β ν : Measure W} [IsProbabilityMeasure β]
    [IsZeroOrProbabilityMeasure ν] (hα : 0 < α) :
    ∏ w, ν {w} ^ (α * β.real {w}) =
      EReal.exp (-((ENNReal.ofReal α * klDiv β ν : ℝ≥0∞) : EReal)) *
        ENNReal.ofReal (Real.exp (-(α * Hm[β]))) := by
  by_cases h : β ≪ ν
  · have : IsProbabilityMeasure ν := (eq_zero_or_isProbabilityMeasure ν).resolve_left fun h0 ↦
      NeZero.ne β (Measure.measure_univ_eq_zero.1 (h (by rw [h0]; rfl)))
    rw [prod_rpow_eq_ofReal_exp h, ← ENNReal.ofReal_toReal (klDiv_ne_top h .of_finite),
      ← ENNReal.ofReal_mul hα.le, EReal.coe_ennreal_ofReal,
      max_eq_left (mul_nonneg hα.le ENNReal.toReal_nonneg), ← EReal.coe_neg, EReal.exp_coe,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    linear_combination α * toReal_klDiv_add_measureEntropy h
  · obtain ⟨w, hν, hβ⟩ : ∃ w, ν {w} = 0 ∧ β {w} ≠ 0 := by
      simpa [Measure.absolutelyContinuous_iff_forall_singleton] using h
    rw [klDiv_of_not_ac h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hα).ne', EReal.coe_ennreal_top,
      EReal.neg_top, EReal.exp_bot, zero_mul]
    refine Finset.prod_eq_zero (Finset.mem_univ w) ?_
    rw [hν, measureReal_def,
      ENNReal.zero_rpow_of_pos (mul_pos hα (ENNReal.toReal_pos hβ (measure_ne_top _ _)))]

/-- For probability beliefs the speaker is the softmax of the negative Kullback–Leibler divergence
of the listener from the belief, less the cost: the divergence and the expected log-probability
differ by the entropy of the belief, which no utterance changes. -/
theorem speaker_eq_speakerOfScore_klDiv [∀ o, IsProbabilityMeasure (b o)]
    [∀ u, IsZeroOrProbabilityMeasure (L u)] (hα : 0 < α) :
    speaker α C L b = speakerOfScore fun o u ↦
      -((ENNReal.ofReal α * klDiv (b o) (L u) : ℝ≥0∞) : EReal) - ((α * C u : ℝ) : EReal) := by
  refine Kernel.ofWeights_eq_of_mul (c := fun o ↦ ENNReal.ofReal (Real.exp (-(α * Hm[b o]))))
    (fun o ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne') (fun _ ↦ ENNReal.ofReal_ne_top)
    fun o u ↦ ?_
  beta_reduce
  rw [sub_eq_add_neg, ← EReal.coe_neg, EReal.exp_add, EReal.exp_coe, prod_rpow_eq_exp_klDiv hα]
  ring

/-- At no cost the speaker prefers the utterance whose listener is closer to her belief. -/
theorem speaker_zero_real_singleton_lt_iff_klDiv [IsProbabilityMeasure (b o)]
    [∀ u, IsZeroOrProbabilityMeasure (L u)] (hα : 0 < α) (h : ∃ u, klDiv (b o) (L u) ≠ ∞) :
    (speaker α 0 L b o).real {u} < (speaker α 0 L b o).real {u'} ↔
      klDiv (b o) (L u') < klDiv (b o) (L u) := by
  have hc0 : ENNReal.ofReal (Real.exp (-(α * Hm[b o]))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hw (v : U) : (∏ w, L v {w} ^ (α * (b o).real {w})) *
      ENNReal.ofReal (Real.exp (-(α * (0 : U → ℝ) v))) =
      EReal.exp (-((ENNReal.ofReal α * klDiv (b o) (L v) : ℝ≥0∞) : EReal)) *
        ENNReal.ofReal (Real.exp (-(α * Hm[b o]))) := by
    rw [prod_rpow_eq_exp_klDiv hα]
    simp
  obtain ⟨u₀, hu₀⟩ := h
  rw [speaker, Kernel.ofWeights_real_singleton_lt_iff o
      (fun h0 ↦ by
        have := Finset.sum_eq_zero_iff.1 h0 u₀ (Finset.mem_univ _)
        rw [hw, mul_eq_zero, or_iff_left hc0, EReal.exp_eq_zero_iff, EReal.neg_eq_bot_iff,
          EReal.coe_ennreal_eq_top_iff, ENNReal.mul_eq_top] at this
        simp [hu₀, hα.not_ge] at this)
      (ENNReal.sum_ne_top.2 fun v _ ↦ by
        rw [hw]
        exact ENNReal.mul_ne_top (mt EReal.exp_eq_top_iff.1
          (mt EReal.neg_eq_top_iff.1 (EReal.coe_ennreal_ne_bot _))) ENNReal.ofReal_ne_top),
    hw, hw, ENNReal.mul_lt_mul_iff_left hc0 ENNReal.ofReal_ne_top, EReal.exp_lt_exp_iff,
    EReal.neg_lt_neg_iff, EReal.coe_ennreal_lt_coe_ennreal_iff,
    ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr hα).ne' ENNReal.ofReal_ne_top]

/-! ### Knowledge against a literal listener

A speaker who knows only that the state lies in an event believes the prior conditioned on it.
Against a literal listener she produces exactly the utterances her knowledge entails, and among
them prefers the one whose extension has the smaller prior mass. -/

section Cond

variable {μ : Measure W} [IsFiniteMeasure μ] {A : O → Set W} {sem : U → Set W}

/-- The speaker produces exactly the utterances her knowledge entails. -/
theorem speaker_cond_literalListener_apply_singleton_eq_zero_iff (hα : 0 < α) :
    speaker α C (literalListener μ sem) (fun o ↦ μ[|A o]) o {u} = 0 ↔ ¬ A o ≤ᵐ[μ] sem u := by
  rw [speaker_apply_singleton_eq_zero_iff_not_ac hα, literalListener_apply,
    cond_absolutelyContinuous_cond_iff .of_discrete .of_discrete]

/-- Among the utterances her knowledge entails, the speaker prefers the one of smaller prior
mass. -/
theorem speaker_zero_cond_literalListener_real_singleton_lt_iff (hα : 0 < α) (hA : μ (A o) ≠ 0)
    (hu : A o ≤ᵐ[μ] sem u) (hu' : A o ≤ᵐ[μ] sem u') :
    (speaker α 0 (literalListener μ sem) (fun o ↦ μ[|A o]) o).real {u} <
        (speaker α 0 (literalListener μ sem) (fun o ↦ μ[|A o]) o).real {u'} ↔
      μ (sem u') < μ (sem u) := by
  have : IsProbabilityMeasure ((fun o ↦ μ[|A o]) o) := cond_isProbabilityMeasure hA
  rw [speaker_zero_real_singleton_lt_iff_klDiv hα ⟨u, mt
      (klDiv_cond_cond_eq_top_iff .of_discrete .of_discrete).1 (not_not.2 hu)⟩,
    literalListener_apply, literalListener_apply,
    klDiv_cond_cond_lt_iff .of_discrete .of_discrete .of_discrete hA hu' hu]

end Cond

end RSA
