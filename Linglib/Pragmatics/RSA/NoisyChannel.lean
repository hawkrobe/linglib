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
speaker composed with the channel (`noisyPragmaticListener`, eq. 8). At the identity channel
each operator is its noiseless counterpart.

## Main definitions

* `RSA.noisyMeaning` — the meaning of a perceived utterance, eq. 6's inner sum.
* `RSA.channelMix` — the listener mass averaged geometrically over the channel.
* `RSA.noisySpeaker` — eq. 7's speaker, `Kernel.ofWeights` of `channelMix ^ α · exp (-(α C))`.
* `RSA.noisyPragmaticListener` — eq. 8, `(N ∘ₖ noisySpeaker N α C L)†μ`.

## Main results

* `RSA.gradedListener_noisyMeaning_id`, `RSA.noisySpeaker_id`,
  `RSA.noisyPragmaticListener_id` — the identity channel recovers `gradedListener`,
  `speaker`, and `pragmaticListener`.
* `RSA.noisySpeaker_real_singleton_lt_iff`, `RSA.noisyPragmaticListener_real_lt_iff` —
  preference reduces to the channel-mixed listener, and to the channelled speaker.
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

/-! ### The pragmatic listener -/

section Listener

variable [Fintype I] [MeasurableSingletonClass I] [MeasurableSingletonClass U] [Countable W]
  [MeasurableSingletonClass W] [StandardBorelSpace W] [Nonempty W] (N : Kernel I U)
  [IsFiniteKernel N] (α : ℝ)
  (C : I → ℝ) (L : Kernel U W) (μ : Measure W) [IsFiniteMeasure μ]

/-- The pragmatic listener over the channel (eq. 8) is the Bayesian inverse, against the
prior, of the speaker followed by the channel. -/
noncomputable def noisyPragmaticListener : Kernel U W := (N ∘ₖ noisySpeaker N α C L)†μ

instance : IsMarkovKernel (noisyPragmaticListener N α C L μ) :=
  inferInstanceAs (IsMarkovKernel ((N ∘ₖ noisySpeaker N α C L)†μ))

/-- Without noise the pragmatic listener is the noiseless one. -/
theorem noisyPragmaticListener_id (C : U → ℝ) (L : Kernel U W) [IsFiniteKernel L] :
    noisyPragmaticListener Kernel.id α C L μ = pragmaticListener α C L μ := by
  simp only [noisyPragmaticListener, noisySpeaker_id, Kernel.id_comp, pragmaticListener]

variable {N α C L μ}

omit [MeasurableSingletonClass I] in
/-- At a prior giving every state the same positive mass, listener preference between two
states is preference of the channelled speaker between them. -/
theorem noisyPragmaticListener_real_lt_iff (hμeq : ∀ w w', μ {w} = μ {w'})
    (hμ0 : ∀ w, μ {w} ≠ 0) {u : U} {w₀ : W} (hs : (N ∘ₖ noisySpeaker N α C L) w₀ {u} ≠ 0)
    {w₁ w₂ : W} :
    (noisyPragmaticListener N α C L μ u).real {w₁} <
        (noisyPragmaticListener N α C L μ u).real {w₂} ↔
      ((N ∘ₖ noisySpeaker N α C L) w₁).real {u} <
        ((N ∘ₖ noisySpeaker N α C L) w₂).real {u} := by
  have hx : ((N ∘ₖ noisySpeaker N α C L) ∘ₘ μ) {u} ≠ 0 :=
    comp_apply_singleton_ne_zero _ _ (hμ0 w₀) hs
  rw [noisyPragmaticListener, posterior_real_singleton _ _ hx, posterior_real_singleton _ _ hx,
    div_lt_div_iff_of_pos_right
      (by rw [measureReal_def]; exact ENNReal.toReal_pos hx (measure_ne_top _ _)),
    show μ.real {w₁} = μ.real {w₂} by rw [measureReal_def, measureReal_def, hμeq],
    mul_lt_mul_iff_of_pos_left
      (by rw [measureReal_def]; exact ENNReal.toReal_pos (hμ0 w₂) (measure_ne_top _ _))]

end Listener

end RSA
