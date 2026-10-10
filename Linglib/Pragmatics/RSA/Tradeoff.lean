module

public import Linglib.Core.InformationTheory.ChannelCapacity
public import Linglib.Pragmatics.RSA.Basic

/-!
# The RSA tradeoff

A speaker observes the state through a kernel and addresses a listener, who hears her utterance
and infers the state. The tradeoff of a speaker and a listener is the conditional entropy of the
utterance given the observation plus the rationality times the expected utility, the listener's
log-probability of the state less the cost of the utterance. The two agents of the Rational
Speech Act recursion are its two partial maximizers. Against a fixed listener the speaker of
`RSA.speaker` at the Bayesian belief maximizes it, and against a fixed speaker the Bayesian
listener does, so a round of the recursion never lowers it.

## Main definitions

* `RSA.expectedUtility`, `RSA.tradeoff`: the expected utility and the tradeoff of a speaker and a
  listener, for a prior over states and an observation kernel.

## Main statements

* `RSA.tradeoff_add_sum_klDiv`, `RSA.tradeoff_le_tradeoff_speaker`: against a fixed listener the
  tradeoff of a speaker falls short of the RSA speaker's by her expected divergence from it.
* `RSA.tradeoff_le_tradeoff_pragmaticListener`: against a fixed speaker the Bayesian listener
  maximizes the tradeoff.
* `RSA.tradeoff_speaker_le_tradeoff_pragmaticListener`,
  `RSA.tradeoff_pragmaticListener_le_tradeoff_speaker`: in a round of the recursion the listener's
  update and the speaker's update each raise the tradeoff, with no condition on the supports.

## Implementation notes

* The speaker's belief is any family `b` that satisfies Bayes' rule with the denominator cleared,
  `(κ ∘ₘ μ) {o} * b o {w} = μ {w} * κ w {o}` on reals. The posterior `κ†μ` is one, and so is the
  point mass for a speaker who observes the state itself (`RSA.id_comp_real_mul_dirac_real`).
* The utility is real-valued, with `Real.log 0 = 0`, where an extended-real utility would be `−∞`
  at a state the listener rules out. The two agree for a speaker who uses no utterance whose
  listener rules out a state she entertains, and the two maximality statements quantify over
  such competitors. Along the recursion the condition holds of itself.
* The source proves the two maximality statements for a speaker who knows the state. The
  statements here, for a speaker who observes it through a kernel, run the same argument with her
  belief in place of the point mass.

## References

* [zaslavsky-hu-levy-2020]
* [goodman-stuhlmuller-2013]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

namespace RSA

variable {W O U : Type*} [MeasurableSpace W] [MeasurableSpace O] [MeasurableSpace U]

/-! ### The rows of the speaker -/

section Row

variable [Fintype W] [Fintype U] [MeasurableSingletonClass U] [Countable O]
  [MeasurableSingletonClass O] {α : ℝ} {C : U → ℝ} {L : U → Measure W}
  [∀ u, IsFiniteMeasure (L u)] {b : O → Measure W} {o : O} {q : Measure U}
  [IsProbabilityMeasure q]

/-- A speaker row that dominates a probability measure is a probability measure. -/
theorem isProbabilityMeasure_speaker_of_absolutelyContinuous (hα : 0 ≤ α)
    (hq : q ≪ speaker α C L b o) : IsProbabilityMeasure (speaker α C L b o) := by
  refine Kernel.isProbabilityMeasure_ofWeights_of_absolutelyContinuous (fun _ ↦ ?_) hq
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα
    (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _)) ENNReal.ofReal_ne_top

variable [MeasurableSingletonClass W] [IsFiniteMeasure (b o)]

/-- Gibbs' variational identity for a speaker row. The divergence of a distribution over
utterances from the row and its entropy add up to the log partition function less `α` times its
expected utility under the speaker's belief. -/
theorem toReal_klDiv_speaker_add_measureEntropy (hα : 0 ≤ α) (hq : q ≪ speaker α C L b o) :
    (klDiv q (speaker α C L b o)).toReal + Hm[q] =
      log (∑ u, ((b o).geomMean (fun w ↦ L u {w}) ^ α).toReal * exp (-(α * C u))) -
        α * ∫ u, (∫ w, log ((L u).real {w}) ∂(b o) - C u) ∂q := by
  have hw (u : U) : (b o).geomMean (fun w ↦ L u {w}) ^ α ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hα (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _)
  have hterm (u : U) : q.real {u} *
        log ((b o).geomMean (fun w ↦ L u {w}) ^ α * ENNReal.ofReal (exp (-(α * C u)))).toReal =
      α * (q.real {u} * (∫ w, log ((L u).real {w}) ∂(b o) - C u)) := by
    rcases eq_or_ne (q {u}) 0 with h | h
    · rw [measureReal_def, h, ENNReal.toReal_zero, zero_mul, zero_mul, mul_zero]
    rcases hα.eq_or_lt with rfl | hα'
    · simp
    have hdom (w : W) (hbw : b o {w} ≠ 0) : L u {w} ≠ 0 := fun hL ↦
      h (hq ((speaker_apply_singleton_eq_zero_iff hα').2 ⟨w, hbw, hL⟩))
    rw [Measure.geomMean_eq_ofReal_exp_sum_log hdom fun _ _ ↦ measure_ne_top _ _,
      ENNReal.ofReal_rpow_of_pos (exp_pos _), ← exp_mul, ← ENNReal.ofReal_mul (exp_pos _).le,
      ← exp_add, ENNReal.toReal_ofReal (exp_pos _).le, log_exp, integral_fintype .of_finite]
    simp only [smul_eq_mul, measureReal_def]
    ring
  have key := toReal_klDiv_ofWeights_add_measureEntropy (μ := q) (i := o)
    (w := fun o u ↦ (b o).geomMean (fun w ↦ L u {w}) ^ α * ENNReal.ofReal (exp (-(α * C u))))
    (fun u ↦ ENNReal.mul_ne_top (hw u) ENNReal.ofReal_ne_top) hq
  simp only [hterm, ← Finset.mul_sum] at key
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le] at key
  rw [integral_fintype .of_finite]
  simp only [smul_eq_mul]
  exact key

/-- Among the distributions it dominates, a speaker row has the greatest entropy plus `α` times
expected utility under her belief. -/
theorem measureEntropy_add_utility_le_speaker (hα : 0 ≤ α) (hq : q ≪ speaker α C L b o) :
    Hm[q] + α * ∫ u, (∫ w, log ((L u).real {w}) ∂(b o) - C u) ∂q ≤
      Hm[speaker α C L b o] +
        α * ∫ u, (∫ w, log ((L u).real {w}) ∂(b o) - C u) ∂(speaker α C L b o) := by
  have := isProbabilityMeasure_speaker_of_absolutelyContinuous hα hq
  have h := toReal_klDiv_speaker_add_measureEntropy hα hq
  have h' := toReal_klDiv_speaker_add_measureEntropy hα
    (Measure.AbsolutelyContinuous.refl (speaker α C L b o))
  rw [klDiv_self, ENNReal.toReal_zero, zero_add] at h'
  linarith [ENNReal.toReal_nonneg (a := klDiv q (speaker α C L b o))]

end Row

/-! ### The tradeoff -/

variable (μ : Measure W) (κ : Kernel W O) (C : U → ℝ) (α : ℝ)

section Defs

variable [Fintype W]

/-- The expected utility of a speaker and a listener averages the listener's log-probability of
the state, less the cost of the utterance, over the states, the speaker's observations and her
utterances. -/
noncomputable def expectedUtility (S : Kernel O U) (L : Kernel U W) : ℝ :=
  ∑ w, μ.real {w} * ∫ u, (log ((L u).real {w}) - C u) ∂((S ∘ₖ κ) w)

variable [Fintype O]

/-- The tradeoff of a speaker and a listener is the conditional entropy of the utterance given the
speaker's observation plus `α` times the expected utility. -/
noncomputable def tradeoff (S : Kernel O U) (L : Kernel U W) : ℝ :=
  ∑ o, (κ ∘ₘ μ).real {o} * Hm[S o] + α * expectedUtility μ κ C S L

/-- For a speaker who observes the state itself the tradeoff averages over the states alone. -/
theorem tradeoff_id (S : Kernel W U) (L : Kernel U W) :
    tradeoff μ Kernel.id C α S L =
      ∑ w, μ.real {w} * Hm[S w] +
        α * ∑ w, μ.real {w} * ∫ u, (log ((L u).real {w}) - C u) ∂(S w) := by
  simp only [tradeoff, expectedUtility, Measure.id_comp, Kernel.comp_id]

end Defs

section Bound

variable [Fintype W] [Fintype O] [Fintype U] [MeasurableSingletonClass W]
  [MeasurableSingletonClass O] [MeasurableSingletonClass U] [IsProbabilityMeasure μ]
  [IsMarkovKernel κ]

/-- The tradeoff is bounded above, by the log of the number of utterances when there is no
cost. -/
theorem tradeoff_le {α : ℝ} (hα : 0 ≤ α) (S : Kernel O U) [IsMarkovKernel S] (L : Kernel U W)
    [IsMarkovKernel L] :
    tradeoff μ κ C α S L ≤ log (Fintype.card U) + α * ∑ u, |C u| := by
  have hV (w : W) : ∫ u, (log ((L u).real {w}) - C u) ∂((S ∘ₖ κ) w) ≤ ∑ u, |C u| :=
    calc ∫ u, (log ((L u).real {w}) - C u) ∂((S ∘ₖ κ) w)
      _ ≤ ∫ _, ∑ u, |C u| ∂((S ∘ₖ κ) w) := integral_mono .of_finite .of_finite fun u ↦ by
          have := Finset.single_le_sum (fun v _ ↦ abs_nonneg (C v)) (Finset.mem_univ u)
          have := log_nonpos measureReal_nonneg (measureReal_le_one (μ := L u) (s := {w}))
          have := neg_abs_le (C u)
          beta_reduce
          linarith
      _ = ∑ u, |C u| := by simp
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ hα)
  · calc ∑ o, (κ ∘ₘ μ).real {o} * Hm[S o]
      _ ≤ ∑ o, (κ ∘ₘ μ).real {o} * log (Fintype.card U) := Finset.sum_le_sum fun o _ ↦
          mul_le_mul_of_nonneg_left (measureEntropy_le_log_card _) measureReal_nonneg
      _ = log (Fintype.card U) := by
          rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]
  · calc expectedUtility μ κ C S L
      _ ≤ ∑ w, μ.real {w} * ∑ u, |C u| := Finset.sum_le_sum fun w _ ↦
          mul_le_mul_of_nonneg_left (hV w) measureReal_nonneg
      _ = ∑ u, |C u| := by rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

end Bound

/-! ### The speaker's step -/

section Speaker

variable [Fintype W] [Fintype O] [Fintype U] [MeasurableSingletonClass W]
  [MeasurableSingletonClass O] [MeasurableSingletonClass U] {μ κ C α} [IsFiniteMeasure μ]
  [IsFiniteKernel κ] {b : O → Measure W} [∀ o, IsFiniteMeasure (b o)]
  (hb : ∀ o w, (κ ∘ₘ μ).real {o} * (b o).real {w} = μ.real {w} * (κ w).real {o})
include hb

/-- The expected utility as the speaker sees it averages, over her observations and utterances,
the listener's log-probability of the state expected under her belief, less the cost. -/
theorem expectedUtility_eq_sum_comp (S : Kernel O U) [IsFiniteKernel S] (L : Kernel U W) :
    expectedUtility μ κ C S L =
      ∑ o, (κ ∘ₘ μ).real {o} * ∫ u, (∫ w, log ((L u).real {w}) ∂(b o) - C u) ∂(S o) := by
  have hrow (o : O) (u : U) :
      (κ ∘ₘ μ).real {o} * (∑ w, (b o).real {w} * log ((L u).real {w}) - C u) =
        ∑ w, μ.real {w} * (κ w).real {o} * (log ((L u).real {w}) - C u) := by
    have h1 : (κ ∘ₘ μ).real {o} * ∑ w, (b o).real {w} * log ((L u).real {w}) =
        ∑ w, μ.real {w} * (κ w).real {o} * log ((L u).real {w}) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ ↦ by rw [← mul_assoc, hb]
    rw [mul_sub, h1, Measure.comp_real_singleton, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ ↦ by ring
  calc expectedUtility μ κ C S L
    _ = ∑ w, ∑ u, ∑ o, (S o).real {u} *
          (μ.real {w} * (κ w).real {o} * (log ((L u).real {w}) - C u)) := by
        simp_rw [expectedUtility, integral_fintype (.of_finite), smul_eq_mul,
          Kernel.comp_real_singleton, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun u _ ↦
          Finset.sum_congr rfl fun o _ ↦ by ring
    _ = ∑ o, ∑ u, ∑ w, (S o).real {u} *
          (μ.real {w} * (κ w).real {o} * (log ((L u).real {w}) - C u)) := by
        rw [Finset.sum_comm]
        exact (Finset.sum_congr rfl fun u _ ↦ Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ o, (κ ∘ₘ μ).real {o} * ∫ u, (∫ w, log ((L u).real {w}) ∂(b o) - C u) ∂(S o) := by
        refine Finset.sum_congr rfl fun o _ ↦ ?_
        rw [integral_fintype .of_finite, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [integral_fintype .of_finite]
        simp only [smul_eq_mul]
        rw [← Finset.mul_sum, ← hrow, mul_left_comm]

variable (hα : 0 ≤ α) (L : Kernel U W) [IsFiniteKernel L]
  (S : Kernel O U) [IsMarkovKernel S] (hS : ∀ o, (κ ∘ₘ μ) {o} ≠ 0 → S o ≪ speaker α C L b o)
include hα hS

/-- Against a fixed listener, the tradeoff of a speaker and her expected divergence from the RSA
speaker add up to the expected log partition function. -/
theorem tradeoff_add_sum_klDiv :
    tradeoff μ κ C α S L +
        ∑ o, (κ ∘ₘ μ).real {o} * (klDiv (S o) (speaker α C L b o)).toReal =
      ∑ o, (κ ∘ₘ μ).real {o} *
        log (∑ u, ((b o).geomMean (fun w ↦ L u {w}) ^ α).toReal * exp (-(α * C u))) := by
  rw [tradeoff, expectedUtility_eq_sum_comp hb S L, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rcases eq_or_ne ((κ ∘ₘ μ) {o}) 0 with h | h
  · simp [measureReal_def, h]
  · linear_combination
      (κ ∘ₘ μ).real {o} * toReal_klDiv_speaker_add_measureEntropy (C := C) hα (hS o h)

/-- Against a fixed listener the speaker at the Bayesian belief maximizes the tradeoff. -/
theorem tradeoff_le_tradeoff_speaker :
    tradeoff μ κ C α S L ≤ tradeoff μ κ C α (speaker α C L b) L := by
  rw [tradeoff, tradeoff, expectedUtility_eq_sum_comp hb S L,
    expectedUtility_eq_sum_comp hb (speaker α C L b) L, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun o _ ↦ ?_
  rcases eq_or_ne ((κ ∘ₘ μ) {o}) 0 with h | h
  · simp [measureReal_def, h]
  · have := mul_le_mul_of_nonneg_left
      (measureEntropy_add_utility_le_speaker (C := C) hα (hS o h))
      (measureReal_nonneg (μ := κ ∘ₘ μ) (s := {o}))
    linarith

end Speaker

/-! ### The listener's step -/

section Listener

variable [Fintype W] [Fintype U] [MeasurableSingletonClass W] [MeasurableSingletonClass U]
  [Nonempty W] [IsProbabilityMeasure μ] [IsMarkovKernel κ] (S : Kernel O U) [IsMarkovKernel S]
  (L : Kernel U W) [IsMarkovKernel L]
  (hL : ∀ u, ((S ∘ₖ κ) ∘ₘ μ) {u} ≠ 0 → ((S ∘ₖ κ)†μ) u ≪ L u)
include hL

/-- Against a fixed speaker the Bayesian listener maximizes the expected utility. -/
theorem expectedUtility_le_pragmaticListener :
    expectedUtility μ κ C S L ≤ expectedUtility μ κ C S (pragmaticListener (S ∘ₖ κ) μ) := by
  have h := sum_mul_integral_log_le (S ∘ₖ κ) μ L hL
  simp_rw [expectedUtility, integral_sub (.of_finite) (.of_finite), mul_sub,
    Finset.sum_sub_distrib]
  exact sub_le_sub_right h _

variable [Fintype O]

/-- Against a fixed speaker the Bayesian listener maximizes the tradeoff. -/
theorem tradeoff_le_tradeoff_pragmaticListener (hα : 0 ≤ α) :
    tradeoff μ κ C α S L ≤ tradeoff μ κ C α S (pragmaticListener (S ∘ₖ κ) μ) :=
  add_le_add_right
    (mul_le_mul_of_nonneg_left (expectedUtility_le_pragmaticListener μ κ C S L hL) hα) _

end Listener

/-! ### A round of the recursion

The side conditions of the two steps hold of themselves along the recursion: the speaker who
answers a listener uses no utterance whose listener rules out a state she entertains, and the
Bayesian listener of a speaker rules out no state at which she might have said the utterance. -/

section Belief

variable {μ κ} [IsFiniteMeasure μ] [IsFiniteKernel κ] {b : O → Measure W} {o : O} {w : W}
  (hb : ∀ o w, (κ ∘ₘ μ).real {o} * (b o).real {w} = μ.real {w} * (κ w).real {o})
include hb

private theorem belief_apply_singleton_ne_zero (hμ : μ {w} ≠ 0) (hκ : κ w {o} ≠ 0) :
    b o {w} ≠ 0 := fun h0 ↦ by
  have h := hb o w
  rw [measureReal_def (b o), h0, ENNReal.toReal_zero, mul_zero, eq_comm, mul_eq_zero,
    measureReal_eq_zero_iff (measure_ne_top _ _),
    measureReal_eq_zero_iff (measure_ne_top _ _)] at h
  exact h.elim hμ hκ

private theorem ne_zero_of_belief_apply_singleton_ne_zero [IsFiniteMeasure (b o)]
    (ho : (κ ∘ₘ μ) {o} ≠ 0) (hbw : b o {w} ≠ 0) : μ {w} ≠ 0 ∧ κ w {o} ≠ 0 := by
  have h : μ.real {w} * (κ w).real {o} ≠ 0 := hb o w ▸ mul_ne_zero
    ((measureReal_eq_zero_iff (measure_ne_top _ _)).not.2 ho)
    ((measureReal_eq_zero_iff (measure_ne_top _ _)).not.2 hbw)
  exact ⟨fun h0 ↦ h (by rw [measureReal_def, h0, ENNReal.toReal_zero, zero_mul]),
    fun h0 ↦ h (by rw [measureReal_def (κ w), h0, ENNReal.toReal_zero, mul_zero])⟩

end Belief

section Round

variable [Fintype W] [Fintype O] [Fintype U] [MeasurableSingletonClass W]
  [MeasurableSingletonClass O] [MeasurableSingletonClass U] {μ κ C α} [Nonempty W]
  [IsProbabilityMeasure μ] [IsMarkovKernel κ] {b : O → Measure W} [∀ o, IsFiniteMeasure (b o)]
  (hb : ∀ o w, (κ ∘ₘ μ).real {o} * (b o).real {w} = μ.real {w} * (κ w).real {o}) (hα : 0 ≤ α)
include hb hα

/-- An utterance a speaker might say at an observation that can occur is one the best response
to her Bayesian listener might say there too. -/
theorem speaker_pragmaticListener_apply_singleton_ne_zero {S : Kernel O U} [IsFiniteKernel S]
    {o : O} {u : U} (ho : (κ ∘ₘ μ) {o} ≠ 0) (hS : S o {u} ≠ 0) :
    speaker α C (pragmaticListener (S ∘ₖ κ) μ) b o {u} ≠ 0 := by
  refine speaker_apply_singleton_ne_zero hα fun w hbw ↦ ?_
  obtain ⟨hμw, hκ⟩ := ne_zero_of_belief_apply_singleton_ne_zero hb ho hbw
  have hSκ : (S ∘ₖ κ) w {u} ≠ 0 := by
    rw [Kernel.comp_apply_singleton]
    exact fun h ↦ mul_ne_zero hκ hS (Finset.sum_eq_zero_iff.1 h o (Finset.mem_univ o))
  exact (pragmaticListener_apply_singleton_ne_zero_iff
    (comp_apply_singleton_ne_zero _ _ hμw hSκ) w).2 ⟨hμw, hSκ⟩

/-- When every observation can occur, the best response to the Bayesian listener of a speaker is
again a probability kernel. -/
theorem isMarkovKernel_speaker_pragmaticListener (hκ : ∀ o, (κ ∘ₘ μ) {o} ≠ 0) (S : Kernel O U)
    [IsMarkovKernel S] : IsMarkovKernel (speaker α C (pragmaticListener (S ∘ₖ κ) μ) b) :=
  ⟨fun o ↦ isProbabilityMeasure_speaker_of_absolutelyContinuous hα (q := S o)
    (Measure.absolutelyContinuous_of_forall_singleton fun _ hu ↦ of_not_not fun hS ↦
      speaker_pragmaticListener_apply_singleton_ne_zero hb hα (hκ o) hS hu)⟩

/-- The speaker's best response to the Bayesian listener of any speaker raises the tradeoff. -/
theorem tradeoff_pragmaticListener_le_tradeoff_speaker (S : Kernel O U) [IsMarkovKernel S] :
    tradeoff μ κ C α S (pragmaticListener (S ∘ₖ κ) μ) ≤
      tradeoff μ κ C α (speaker α C (pragmaticListener (S ∘ₖ κ) μ) b)
        (pragmaticListener (S ∘ₖ κ) μ) :=
  tradeoff_le_tradeoff_speaker hb hα _ S fun _ ho ↦
    Measure.absolutelyContinuous_of_forall_singleton fun _ hu ↦ of_not_not fun hS ↦
      speaker_pragmaticListener_apply_singleton_ne_zero hb hα ho hS hu

/-- The listener's Bayesian update to the speaker who answers her raises the tradeoff. -/
theorem tradeoff_speaker_le_tradeoff_pragmaticListener (L : Kernel U W) [IsMarkovKernel L]
    [IsMarkovKernel (speaker α C L b)] :
    tradeoff μ κ C α (speaker α C L b) L ≤
      tradeoff μ κ C α (speaker α C L b) (pragmaticListener (speaker α C L b ∘ₖ κ) μ) := by
  rcases hα.eq_or_lt with rfl | hα'
  · simp [tradeoff]
  refine tradeoff_le_tradeoff_pragmaticListener μ κ C α _ L (fun u hu ↦
    Measure.absolutelyContinuous_of_forall_singleton fun w hL ↦ of_not_not fun hpost ↦ ?_) hα
  obtain ⟨hμw, hSw⟩ := (posterior_apply_singleton_ne_zero_iff _ _ hu w).1 hpost
  rw [Kernel.comp_apply_singleton] at hSw
  obtain ⟨o, -, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero hSw
  exact right_ne_zero_of_mul ho ((speaker_apply_singleton_eq_zero_iff hα').2
    ⟨w, belief_apply_singleton_ne_zero hb hμw (left_ne_zero_of_mul ho), hL⟩)

end Round

/-! ### The speaker who knows the state -/

/-- A speaker who observes the state itself believes the point mass there. -/
theorem id_comp_real_mul_dirac_real [MeasurableSingletonClass W] (o w : W) :
    ((Kernel.id : Kernel W W) ∘ₘ μ).real {o} * (Measure.dirac o).real {w} =
      μ.real {w} * ((Kernel.id : Kernel W W) w).real {o} := by
  rw [Measure.id_comp, Kernel.id_apply]
  rcases eq_or_ne o w with rfl | h
  · simp
  · simp [measureReal_def, Measure.dirac_apply', h, h.symm]

end RSA
