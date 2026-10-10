module

public import Linglib.Core.InformationTheory.Entropy
public import Linglib.Core.InformationTheory.KullbackLeibler.Cond
public import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Pragmatics.RSA.Basic

/-!
# Speakers with beliefs

A speaker who does not know the state believes a measure on states. `RSA.speaker` scores an
utterance by the expected log-probability its listener gives the state under that belief, as
Goodman and Stuhlmüller do. This file relates that score to the Kullback–Leibler divergence of the
listener's posterior from the belief: the two differ by the entropy of the belief, which no
utterance changes, so they define the same speaker. An utterance whose listener rules out a state
the speaker entertains is never produced, and against a listener who reweights a prior the prior
cancels from her choice.

## Main results

* `RSA.speaker_apply_singleton_eq_zero_iff`: the speaker produces exactly the utterances whose
  listener rules out no state she entertains.
* `RSA.speaker_eq_speakerOfScore_sum_log`, `RSA.speaker_eq_speakerOfScore_klDiv`: the speaker is
  the softmax of the expected log-probability the listener gives the state under her belief, and
  of the negative divergence of the listener from her belief.
* `RSA.speaker_gradedListener_apply_singleton`: against a graded listener she weighs an
  utterance by the geometric mean of its meaning over her belief and the inverse of the meaning's
  prior mass.
* `RSA.speaker_cond_literalListener_apply_eq`,
  `RSA.speaker_zero_cond_literalListener_real_singleton_lt_iff`: a speaker whose belief is the
  prior conditioned on what she knows depends on it, against a literal listener, only through
  the utterances it entails, and among those prefers the one of smaller prior mass.

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
of the listener from the belief, less the cost, since the divergence and the expected
log-probability differ by the entropy of the belief, which no utterance changes. -/
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

/-! ### Belief against a graded listener

A graded listener reweights the prior by the meaning of the utterance. The prior, which no
utterance changes, cancels from the speaker's choice, and she weighs an utterance by the geometric
mean of its meaning over her belief against the meaning's prior mass. -/

section Graded

variable {μ : Measure W} {m : U → W → ℝ≥0∞}

private theorem prod_gradedListener_rpow {β : Measure W} [IsProbabilityMeasure β] (hα : 0 ≤ α)
    (u : U) :
    ∏ w, gradedListener μ m u {w} ^ (α * β.real {w}) =
      (∏ w, μ {w} ^ (α * β.real {w})) *
        ((∏ w, m u w ^ (α * β.real {w})) * (∑ w, m u w * μ {w})⁻¹ ^ α) := by
  have he (w : W) : 0 ≤ α * β.real {w} := mul_nonneg hα measureReal_nonneg
  calc ∏ w, gradedListener μ m u {w} ^ (α * β.real {w})
    _ = ∏ w, μ {w} ^ (α * β.real {w}) *
          (m u w ^ (α * β.real {w}) * (∑ w', m u w' * μ {w'})⁻¹ ^ (α * β.real {w})) :=
        Finset.prod_congr rfl fun w _ ↦ by
          rw [gradedListener_apply_singleton, div_eq_mul_inv,
            ENNReal.mul_rpow_of_nonneg _ _ (he w), ENNReal.mul_rpow_of_nonneg _ _ (he w)]
          ring
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          ← ENNReal.rpow_sum_of_nonneg _ fun w _ ↦ he w, ← Finset.mul_sum,
          sum_measureReal_singleton_eq_one, mul_one]

variable [IsFiniteMeasure μ]

/-- Against a graded listener the speaker weighs an utterance by the geometric mean of its
meaning over her belief and by the inverse of the meaning's prior mass. -/
theorem speaker_gradedListener_apply_singleton (hα : 0 ≤ α) [IsProbabilityMeasure (b o)]
    (hb : b o ≪ μ) (u : U) :
    speaker α C (gradedListener μ m) b o {u} =
      (∏ w, m u w ^ (α * (b o).real {w})) * ((∑ w, m u w * μ {w})⁻¹ ^ α *
          ENNReal.ofReal (Real.exp (-(α * C u)))) /
        ∑ u', (∏ w, m u' w ^ (α * (b o).real {w})) * ((∑ w, m u' w * μ {w})⁻¹ ^ α *
          ENNReal.ofReal (Real.exp (-(α * C u')))) := by
  have he (w : W) : 0 ≤ α * (b o).real {w} := mul_nonneg hα measureReal_nonneg
  have h0 : ∏ w, μ {w} ^ (α * (b o).real {w}) ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ h ↦ by
    rcases ENNReal.rpow_eq_zero_iff.1 h with ⟨hμ, hpos⟩ | ⟨hμ, -⟩
    · rw [measureReal_def, hb hμ, ENNReal.toReal_zero, mul_zero] at hpos
      exact lt_irrefl _ hpos
    · exact measure_ne_top μ _ hμ
  have htop : ∏ w, μ {w} ^ (α * (b o).real {w}) ≠ ∞ :=
    ENNReal.prod_ne_top fun w _ ↦ ENNReal.rpow_ne_top_of_nonneg (he w) (measure_ne_top μ _)
  simp only [speaker_apply_singleton, prod_gradedListener_rpow hα, mul_assoc]
  rw [← Finset.mul_sum, ENNReal.mul_div_mul_left _ _ h0 htop]

/-- Against a graded listener, two observations at which every meaning has the same geometric
mean over the speaker's belief yield the same speaker. -/
theorem speaker_gradedListener_apply_congr (hα : 0 ≤ α) {o₁ o₂ : O}
    [IsProbabilityMeasure (b o₁)] [IsProbabilityMeasure (b o₂)] (h₁ : b o₁ ≪ μ) (h₂ : b o₂ ≪ μ)
    (h : ∀ u, ∏ w, m u w ^ (α * (b o₂).real {w}) = ∏ w, m u w ^ (α * (b o₁).real {w})) :
    speaker α C (gradedListener μ m) b o₂ = speaker α C (gradedListener μ m) b o₁ :=
  Measure.ext_of_singleton fun u ↦ by
    simp only [speaker_gradedListener_apply_singleton hα h₂,
      speaker_gradedListener_apply_singleton hα h₁, h]

end Graded

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

private theorem cond_apply_singleton_ne_zero_iff {s : Set W} {w : W} :
    μ[|s] {w} ≠ 0 ↔ w ∈ s ∧ μ {w} ≠ 0 := by
  by_cases hw : w ∈ s <;>
    simp [cond_apply (μ := μ) (MeasurableSet.of_discrete (s := s)), hw, measure_ne_top]

/-- A speaker who knows an event on which every graded meaning is constant sees the listener only
through those constants, so two such events with the same constants yield the same speaker. -/
theorem speaker_cond_gradedListener_apply_eq {m : U → W → ℝ≥0∞} (hα : 0 ≤ α) {o₁ o₂ : O}
    (h₁ : μ (A o₁) ≠ 0) (h₂ : μ (A o₂) ≠ 0) {g : U → ℝ≥0∞}
    (hg₁ : ∀ u, ∀ w ∈ A o₁, μ {w} ≠ 0 → m u w = g u)
    (hg₂ : ∀ u, ∀ w ∈ A o₂, μ {w} ≠ 0 → m u w = g u) :
    speaker α C (gradedListener μ m) (fun o ↦ μ[|A o]) o₂ =
      speaker α C (gradedListener μ m) (fun o ↦ μ[|A o]) o₁ := by
  have : IsProbabilityMeasure ((fun o ↦ μ[|A o]) o₁) := cond_isProbabilityMeasure h₁
  have : IsProbabilityMeasure ((fun o ↦ μ[|A o]) o₂) := cond_isProbabilityMeasure h₂
  refine speaker_gradedListener_apply_congr hα cond_absolutelyContinuous
    cond_absolutelyContinuous fun u ↦ ?_
  rw [prod_rpow_measureReal_of_forall_eq _ hα fun w hw ↦
      hg₂ u w (cond_apply_singleton_ne_zero_iff.1 hw).1 (cond_apply_singleton_ne_zero_iff.1 hw).2,
    prod_rpow_measureReal_of_forall_eq _ hα fun w hw ↦
      hg₁ u w (cond_apply_singleton_ne_zero_iff.1 hw).1 (cond_apply_singleton_ne_zero_iff.1 hw).2]

private theorem prod_indicator_rpow_cond (hα : 0 < α) {s t : Set W} (hs : μ s ≠ 0)
    [Decidable (s ≤ᵐ[μ] t)] :
    ∏ w, t.indicator (1 : W → ℝ≥0∞) w ^ (α * μ[|s].real {w}) = if s ≤ᵐ[μ] t then 1 else 0 := by
  have := cond_isProbabilityMeasure (μ := μ) hs
  split_ifs with h
  · rw [prod_rpow_measureReal_of_forall_eq _ hα.le (c := 1) fun w hw ↦ Set.indicator_of_mem
      (ae_iff_of_countable.1 h w (cond_apply_singleton_ne_zero_iff.1 hw).2
        (cond_apply_singleton_ne_zero_iff.1 hw).1) 1, ENNReal.one_rpow]
  · obtain ⟨w, hμ, hws, hwt⟩ : ∃ w, μ {w} ≠ 0 ∧ w ∈ s ∧ w ∉ t := by
      by_contra hne
      exact h (ae_iff_of_countable.2 fun w hμ hws ↦ by_contra fun hwt ↦ hne ⟨w, hμ, hws, hwt⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by
      rw [Set.indicator_of_notMem hwt, measureReal_def, ENNReal.zero_rpow_of_pos (mul_pos hα
        (ENNReal.toReal_pos
          (cond_apply_singleton_ne_zero_iff.2 ⟨hws, hμ⟩) (measure_ne_top _ _)))])

/-- Against a literal listener the speaker depends on what she knows only through the utterances
it entails. -/
theorem speaker_cond_literalListener_apply_eq (hα : 0 < α) {o₁ o₂ : O} (h₁ : μ (A o₁) ≠ 0)
    (h₂ : μ (A o₂) ≠ 0) (h : ∀ u, A o₂ ≤ᵐ[μ] sem u ↔ A o₁ ≤ᵐ[μ] sem u) :
    speaker α C (literalListener μ sem) (fun o ↦ μ[|A o]) o₂ =
      speaker α C (literalListener μ sem) (fun o ↦ μ[|A o]) o₁ := by
  classical
  have : IsProbabilityMeasure ((fun o ↦ μ[|A o]) o₁) := cond_isProbabilityMeasure h₁
  have : IsProbabilityMeasure ((fun o ↦ μ[|A o]) o₂) := cond_isProbabilityMeasure h₂
  rw [← gradedListener_indicator]
  refine speaker_gradedListener_apply_congr hα.le cond_absolutelyContinuous
    cond_absolutelyContinuous fun u ↦ ?_
  rw [prod_indicator_rpow_cond hα h₂, prod_indicator_rpow_cond hα h₁]
  exact if_congr (h u) rfl rfl

end Cond

end RSA
