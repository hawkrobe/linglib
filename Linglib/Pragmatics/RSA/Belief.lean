module

public import Linglib.Core.InformationTheory.Entropy
public import Linglib.Core.InformationTheory.KullbackLeibler.Cond
public import Linglib.Pragmatics.RSA.Basic

/-!
# Speakers with beliefs

A speaker who does not know the state holds a belief about it, a measure on states, and wants the
listener to come to share it. Goodman and Stuhlmüller score an utterance by the expected
log-probability its listener gives the state under her belief. Up to the entropy of the belief,
which no utterance changes, this is the negative Kullback–Leibler divergence of the listener's
posterior from the belief, the utility of the speaker defined here. An utterance whose listener
rules out a state she entertains is at infinite divergence and is never produced.

## Main definitions

* `RSA.beliefSpeaker`: the softmax of the negative divergence of the listener from the belief.

## Main results

* `RSA.beliefSpeaker_real_singleton_lt_iff`: the speaker prefers the utterance whose listener is
  closer to her belief.
* `RSA.beliefSpeaker_eq_speakerOfScore_sum_log`: the speaker is the softmax of the expected
  log-probability the listener gives the state under her belief.
* `RSA.beliefSpeaker_dirac`: a speaker who knows the state is the informativity speaker.
* `RSA.beliefSpeaker_cond_literalListener_real_singleton_lt_iff`: a speaker whose belief is the
  prior conditioned on what she knows prefers, among the utterances her knowledge entails, the
  one of smaller prior mass.

## References

* [goodman-stuhlmuller-2013]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace RSA

variable {W U O : Type*} [MeasurableSpace W] {α : ℝ} {b : O → Measure W} {L : U → Measure W}
  {o : O} {u u' : U}

private theorem score_ne_top (α : ℝ) (b : O → Measure W) (L : U → Measure W) (o : O) (u : U) :
    -((ENNReal.ofReal α * klDiv (b o) (L u) : ℝ≥0∞) : EReal) ≠ ⊤ :=
  mt EReal.neg_eq_top_iff.mp (EReal.coe_ennreal_ne_bot _)

private theorem score_eq_bot_iff (hα : 0 < α) :
    -((ENNReal.ofReal α * klDiv (b o) (L u) : ℝ≥0∞) : EReal) = ⊥ ↔ klDiv (b o) (L u) = ∞ := by
  rw [EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff, ENNReal.mul_eq_top]
  simp [ENNReal.ofReal_eq_zero, hα.not_ge]

variable [MeasurableSpace U] [MeasurableSpace O] [Countable O] [MeasurableSingletonClass O]
  [Fintype U]

/-- At an observation `o` the belief speaker at rationality `α` holds the belief `b o` about the
state and scores an utterance by the negative divergence of its listener `L u` from that
belief. -/
noncomputable def beliefSpeaker (α : ℝ) (b : O → Measure W) (L : U → Measure W) : Kernel O U :=
  speakerOfScore fun o u ↦ -((ENNReal.ofReal α * klDiv (b o) (L u) : ℝ≥0∞) : EReal)

instance (α : ℝ) (b : O → Measure W) (L : U → Measure W) : IsFiniteKernel (beliefSpeaker α b L) :=
  inferInstanceAs (IsFiniteKernel (speakerOfScore _))

/-- The belief speaker is a probability kernel whenever every observation has an utterance at
finite divergence. -/
theorem isMarkovKernel_beliefSpeaker (hα : 0 < α) (h : ∀ o, ∃ u, klDiv (b o) (L u) ≠ ∞) :
    IsMarkovKernel (beliefSpeaker α b L) :=
  isMarkovKernel_speakerOfScore (fun o ↦ (h o).imp fun _ hu ↦ mt (score_eq_bot_iff hα).1 hu)
    fun o u ↦ score_ne_top α b L o u

/-- A speaker who knows the state is the informativity speaker at no cost. -/
theorem beliefSpeaker_dirac [Countable W] [MeasurableSingletonClass W] (hα : 0 ≤ α)
    (L : Kernel U W) [∀ u, IsZeroOrProbabilityMeasure (L u)] :
    beliefSpeaker α Measure.dirac L = speaker α 0 L := by
  refine congrArg speakerOfScore (funext fun w ↦ funext fun u ↦ ?_)
  rw [EReal.coe_ennreal_mul, coe_klDiv_dirac_left, EReal.coe_ennreal_ofReal, max_eq_left hα,
    utility, Pi.zero_apply, EReal.coe_zero, sub_zero, mul_neg, neg_neg, mul_comm]

variable [MeasurableSingletonClass U]

/-- An utterance at infinite divergence from the belief is never produced. -/
theorem beliefSpeaker_apply_singleton_eq_zero (hα : 0 < α) (h : klDiv (b o) (L u) = ∞) :
    beliefSpeaker α b L o {u} = 0 :=
  speakerOfScore_apply_singleton_eq_zero ((score_eq_bot_iff hα).2 h)

/-- An utterance at finite divergence from the belief is produced with positive mass. -/
theorem beliefSpeaker_apply_singleton_ne_zero (hα : 0 < α) (h : klDiv (b o) (L u) ≠ ∞) :
    beliefSpeaker α b L o {u} ≠ 0 :=
  speakerOfScore_apply_singleton_ne_zero (mt (score_eq_bot_iff hα).1 h) (score_ne_top α b L o)

theorem beliefSpeaker_apply_singleton_eq_zero_iff (hα : 0 < α) :
    beliefSpeaker α b L o {u} = 0 ↔ klDiv (b o) (L u) = ∞ :=
  ⟨fun h ↦ by_contra fun hne ↦ beliefSpeaker_apply_singleton_ne_zero hα hne h,
    beliefSpeaker_apply_singleton_eq_zero hα⟩

/-- The speaker prefers the utterance whose listener is closer to her belief. -/
theorem beliefSpeaker_real_singleton_lt_iff (hα : 0 < α) (h : ∃ u, klDiv (b o) (L u) ≠ ∞) :
    (beliefSpeaker α b L o).real {u} < (beliefSpeaker α b L o).real {u'} ↔
      klDiv (b o) (L u') < klDiv (b o) (L u) := by
  rw [beliefSpeaker, speakerOfScore_real_singleton_lt_iff (score_ne_top α b L o)
    (h.imp fun _ hu ↦ mt (score_eq_bot_iff hα).1 hu), EReal.neg_lt_neg_iff,
    EReal.coe_ennreal_lt_coe_ennreal_iff,
    ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr hα).ne' ENNReal.ofReal_ne_top]

/-- When every listener dominates every belief, the belief speaker is the softmax of the expected
log-probability the listener gives the state under the belief. The two utilities differ by the
entropy of the belief, which no utterance changes. -/
theorem beliefSpeaker_eq_speakerOfScore_sum_log [Fintype W] [MeasurableSingletonClass W]
    [∀ o, IsProbabilityMeasure (b o)] [∀ u, IsProbabilityMeasure (L u)] (hα : 0 ≤ α)
    (h : ∀ o u, b o ≪ L u) :
    beliefSpeaker α b L = speakerOfScore fun o u ↦
      ((α * ∑ w, (b o).real {w} * Real.log ((L u).real {w}) : ℝ) : EReal) := by
  refine speakerOfScore_eq_of_add (k := fun o ↦ α * Hm[b o]) fun o u ↦ ?_
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top (h o u) .of_finite), ← ENNReal.ofReal_mul hα,
    EReal.coe_ennreal_ofReal, max_eq_left (mul_nonneg hα ENNReal.toReal_nonneg), ← EReal.coe_neg,
    ← EReal.coe_add, EReal.coe_eq_coe_iff]
  linear_combination -α * toReal_klDiv_add_measureEntropy (h o u)

/-! ### Knowledge against a literal listener

A speaker who knows only that the state lies in an event believes the prior conditioned on it.
Against a literal listener her divergence is the log ratio of the prior masses of the
utterance's extension and of what she knows, when her knowledge entails the utterance, and
infinite otherwise. -/

section Cond

variable [DiscreteMeasurableSpace W] {μ : Measure W} [IsFiniteMeasure μ] {A : O → Set W}
  {sem : U → Set W}

/-- The speaker produces exactly the utterances her knowledge entails. -/
theorem beliefSpeaker_cond_literalListener_apply_singleton_eq_zero_iff (hα : 0 < α) :
    beliefSpeaker α (fun o ↦ μ[|A o]) (literalListener μ sem) o {u} = 0 ↔ ¬ A o ≤ᵐ[μ] sem u := by
  rw [beliefSpeaker_apply_singleton_eq_zero_iff hα, literalListener_apply,
    klDiv_cond_cond_eq_top_iff .of_discrete .of_discrete]

/-- Among the utterances her knowledge entails, the speaker prefers the one of smaller prior
mass. -/
theorem beliefSpeaker_cond_literalListener_real_singleton_lt_iff (hα : 0 < α) (hA : μ (A o) ≠ 0)
    (hu : A o ≤ᵐ[μ] sem u) (hu' : A o ≤ᵐ[μ] sem u') :
    (beliefSpeaker α (fun o ↦ μ[|A o]) (literalListener μ sem) o).real {u} <
        (beliefSpeaker α (fun o ↦ μ[|A o]) (literalListener μ sem) o).real {u'} ↔
      μ (sem u') < μ (sem u) := by
  rw [beliefSpeaker_real_singleton_lt_iff hα ⟨u, mt
      (klDiv_cond_cond_eq_top_iff .of_discrete .of_discrete).1 (not_not.2 hu)⟩,
    literalListener_apply, literalListener_apply,
    klDiv_cond_cond_lt_iff .of_discrete .of_discrete .of_discrete hA hu' hu]

end Cond

end RSA
