module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Core.Probability.Kernel.Composition.Lemmas

/-!
# Rational speech acts over a noisy channel

Bergen and Goodman extend the pipeline of `Linglib.Pragmatics.RSA.Basic` with a channel
`N : Kernel I U` from the speaker's intended utterances to the perceived ones. The literal
listener decodes before interpreting, so the meaning of a perceived utterance is the meaning of
each intended one weighted by the utterance prior and the channel (`noisyMeaning`, eq. 6). The
speaker's informativity is the channel-expected log listener, whose exponential is the listener
mass averaged geometrically over perceptions (`channelMix`), and the speaker is the power-weight
best response to that mix (`noisySpeaker`, eqs. 4 and 7). The pragmatic listener inverts the
speaker composed with the channel (eq. 8). At the identity channel each operator is its noiseless
counterpart.

## Main definitions

* `RSA.noisyMeaning` — the meaning of a perceived utterance, eq. 6's inner sum.
* `RSA.channelMix` — the listener mass averaged geometrically over the channel.
* `RSA.noisySpeaker` — eq. 7's speaker, `Kernel.ofWeights` of `channelMix ^ α · exp (-(α C))`.

## Main results

* `RSA.gradedListener_noisyMeaning_id`, `RSA.noisySpeaker_id`,
  `RSA.pragmaticListener_id_comp_noisySpeaker` — the identity channel recovers `gradedListener`,
  `speaker`, and `pragmaticListener`.
* `RSA.noisySpeaker_real_singleton_lt_iff` — preference reduces to the channel-mixed
  listener.
* `RSA.channelMix_eq_prod` — the mix over the perceptions the channel can produce.

## References

* [bergen-goodman-2015]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace RSA

variable {W I U : Type*} [MeasurableSpace I] [MeasurableSpace U] [Fintype U]

/-! ### The decoded meaning -/

section Meaning

/-- The meaning of a perceived utterance `u_p` is the meaning of each intended utterance,
weighted by the utterance prior and the channel (eq. 6). -/
noncomputable def noisyMeaning (N : Kernel I U) (π : Measure I) (m : I → W → ℝ≥0∞) (u_p : U)
    (w : W) : ℝ≥0∞ :=
  ∫⁻ u_i, N u_i {u_p} * m u_i w ∂π

variable [Fintype I] [MeasurableSingletonClass I]

omit [Fintype U] in
theorem noisyMeaning_apply (N : Kernel I U) (π : Measure I) (m : I → W → ℝ≥0∞) (u_p : U)
    (w : W) : noisyMeaning N π m u_p w = ∑ u_i, N u_i {u_p} * m u_i w * π {u_i} :=
  lintegral_fintype _

variable [MeasurableSingletonClass U]

/-- Without noise the perceived utterance is the intended one, weighted by its prior. -/
theorem noisyMeaning_id (π : Measure U) (m : U → W → ℝ≥0∞) (u : U) (w : W) :
    noisyMeaning Kernel.id π m u w = π {u} * m u w := by
  rw [noisyMeaning_apply, sum_eq_single u]
  · rw [Kernel.id_apply, Measure.dirac_apply_of_mem (Set.mem_singleton u), one_mul, mul_comm]
  · intro v _ hv
    rw [Kernel.id_apply, Measure.dirac_apply' _ (.singleton u),
      Set.indicator_of_notMem (Set.notMem_singleton_iff.mpr hv), zero_mul, zero_mul]
  · exact fun h => absurd (mem_univ u) h

end Meaning

variable [MeasurableSpace W]

/-! ### The speaker -/

section Speaker

/-- `channelMix N L u_i w` averages the listener mass at `w` geometrically over the
perceptions of `u_i`; it is the exponential of the channel-expected log listener, eq. 7's
informativity. -/
noncomputable def channelMix (N : Kernel I U) (L : Kernel U W) (u_i : I) (w : W) : ℝ≥0∞ :=
  ∏ u_p, L u_p {w} ^ (N u_i {u_p}).toReal

/-- The mix over the perceptions the channel can produce. -/
theorem channelMix_eq_prod (N : Kernel I U) (L : Kernel U W) {u_i : I} {s : Finset U}
    (hs : ∀ u_p ∉ s, N u_i {u_p} = 0) (w : W) :
    channelMix N L u_i w = ∏ u_p ∈ s, L u_p {w} ^ (N u_i {u_p}).toReal :=
  (prod_subset (subset_univ s) fun u_p _ hu => by
    rw [hs u_p hu, ENNReal.toReal_zero, ENNReal.rpow_zero]).symm

theorem channelMix_ne_top (N : Kernel I U) (L : Kernel U W) [IsFiniteKernel L] (u_i : I)
    (w : W) : channelMix N L u_i w ≠ ∞ :=
  ENNReal.prod_ne_top fun _ _ => ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
    (measure_ne_top _ _)

variable [MeasurableSingletonClass U]

/-- Without noise the literal listener is the noiseless one at every utterance of positive
finite prior mass. -/
theorem gradedListener_noisyMeaning_id (μ : Measure W) (π : Measure U) (m : U → W → ℝ≥0∞)
    {u : U} (h0 : π {u} ≠ 0) (htop : π {u} ≠ ∞) :
    gradedListener μ (noisyMeaning Kernel.id π m) u = gradedListener μ m u :=
  gradedListener_apply_eq_of_eq_mul μ h0 htop (noisyMeaning_id π m u)

theorem channelMix_id (L : Kernel U W) (u : U) (w : W) : channelMix Kernel.id L u w = L u {w} := by
  rw [channelMix_eq_prod _ _ (s := {u}) fun v hv => by
      rw [Kernel.id_apply, Measure.dirac_apply' _ (.singleton v),
        Set.indicator_of_notMem (Set.notMem_singleton_iff.mpr fun h => hv (by simp [h]))],
    prod_singleton, Kernel.id_apply, Measure.dirac_apply_of_mem (Set.mem_singleton u),
    ENNReal.toReal_one, ENNReal.rpow_one]

variable [Fintype I] [MeasurableSingletonClass I] [Countable W] [MeasurableSingletonClass W]

/-- The speaker over the channel (eqs. 4 and 7) weights each utterance by the channel-mixed
listener to the power `α`, scaled by the cost weight `exp (-(α * C u))`. -/
noncomputable def noisySpeaker (N : Kernel I U) (α : ℝ) (C : I → ℝ) (L : Kernel U W) :
    Kernel W I :=
  Kernel.ofWeights fun w u => channelMix N L u w ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))

omit [MeasurableSingletonClass U] in
@[simp] theorem noisySpeaker_apply_singleton (N : Kernel I U) (α : ℝ) (C : I → ℝ)
    (L : Kernel U W) (w : W) (u : I) :
    noisySpeaker N α C L w {u} =
      channelMix N L u w ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))
        / ∑ u', channelMix N L u' w ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) :=
  Kernel.ofWeights_apply_singleton _ w u

instance (N : Kernel I U) (α : ℝ) (C : I → ℝ) (L : Kernel U W) :
    IsFiniteKernel (noisySpeaker N α C L) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

omit [MeasurableSingletonClass U] in
/-- Row preference of the speaker reduces to comparing the weighted channel-mixed listener
values; the normalization cancels. -/
theorem noisySpeaker_real_singleton_lt_iff {N : Kernel I U} {α : ℝ} (hα : 0 ≤ α) {C : I → ℝ}
    {L : Kernel U W} [IsFiniteKernel L] {w : W}
    (h0 : ∃ u, channelMix N L u w ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) ≠ 0) {u u' : I} :
    (noisySpeaker N α C L w).real {u} < (noisySpeaker N α C L w).real {u'} ↔
      channelMix N L u w ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))
        < channelMix N L u' w ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) :=
  Kernel.ofWeights_real_singleton_lt_iff w
    (fun h => let ⟨u₀, hu₀⟩ := h0; hu₀ (sum_eq_zero_iff.mp h u₀ (mem_univ _)))
    (ENNReal.sum_ne_top.mpr fun u _ => ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hα (channelMix_ne_top N L u w)) ENNReal.ofReal_ne_top)

/-- Without noise the speaker is the noiseless one. -/
theorem noisySpeaker_id (α : ℝ) (C : U → ℝ) (L : Kernel U W) [IsFiniteKernel L] :
    noisySpeaker Kernel.id α C L = speaker α C L := by
  rw [speaker_eq_ofWeights]
  unfold noisySpeaker
  congr 1
  funext w u
  rw [channelMix_id]

end Speaker

/-! ### The pragmatic listener

The pragmatic listener over the channel (eq. 8) is
`pragmaticListener (N ∘ₖ noisySpeaker N α C L) μ`, the Bayesian inverse, against the prior, of
the speaker followed by the channel. -/

section Listener

variable [MeasurableSingletonClass U] [Countable W] [MeasurableSingletonClass W]
  [StandardBorelSpace W] [Nonempty W]

/-- Without noise the pragmatic listener over the channel is the noiseless one. -/
theorem pragmaticListener_id_comp_noisySpeaker (α : ℝ) (C : U → ℝ) (L : Kernel U W)
    [IsFiniteKernel L] (μ : Measure W) [IsFiniteMeasure μ] :
    pragmaticListener (Kernel.id ∘ₖ noisySpeaker Kernel.id α C L) μ =
      pragmaticListener (speaker α C L) μ := by
  simp only [noisySpeaker_id, Kernel.id_comp]

end Listener

end RSA
