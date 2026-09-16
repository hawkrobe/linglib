import Linglib.Pragmatics.RSA.Basic
import Linglib.Core.Probability.Kernel.Composition.Lemmas

/-!
# Rational speech acts over a noisy channel

[bergen-goodman-2015]'s extension of the pipeline of `Linglib.Pragmatics.RSA.Basic` to a
channel `N : Kernel U U` from intended to perceived utterances. The literal listener decodes
before interpreting: the meaning of a perceived utterance is the meaning of each intended one,
weighted by the utterance prior and the channel (`noisyMeaning`, eq. 6). The speaker's
informativity is the channel-expected log listener, whose exponential is the listener mass
averaged geometrically over perceptions (`channelMix`), so the speaker is the power-weight best
response to that mix (`noisySpeaker`, eqs. 4 and 7). The pragmatic listener inverts the speaker
composed with the channel (`noisyPragmaticListener`, eq. 8). At the identity channel each
operator is its noiseless counterpart.

## Main definitions

* `RSA.noisyMeaning` — the meaning of a perceived utterance, eq. 6's inner sum.
* `RSA.channelMix` — the listener mass averaged geometrically over the channel.
* `RSA.noisySpeaker` — eq. 7's speaker, `Kernel.ofWeights` of `channelMix ^ α · cost`.
* `RSA.noisyPragmaticListener` — eq. 8, `(N ∘ₖ noisySpeaker N α cost L)†μ`.

## Main results

* `RSA.literalListener_noisyMeaning_id`, `RSA.noisySpeaker_id`,
  `RSA.noisyPragmaticListener_id` — the identity channel recovers `literalListener`,
  `speaker`, and `pragmaticListener`.
* `RSA.noisySpeaker_real_singleton_lt_iff`, `RSA.noisyPragmaticListener_real_lt_iff` —
  preference reduces to the channel-mixed listener, and to the channelled speaker.
* `RSA.channelMix_eq_prod` — the mix over the perceptions the channel can produce.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace RSA

variable {W U : Type*} [MeasurableSpace U] [Fintype U]

/-! ### The decoded meaning -/

section Meaning

variable [MeasurableSingletonClass U]

/-- The meaning of a perceived utterance `u_p`: the meaning of each intended utterance,
weighted by the utterance prior and the channel (eq. 6). -/
noncomputable def noisyMeaning (N : Kernel U U) (π : Measure U) (m : U → W → ℝ≥0∞) (u_p : U)
    (w : W) : ℝ≥0∞ :=
  ∫⁻ u_i, N u_i {u_p} * m u_i w ∂π

theorem noisyMeaning_apply (N : Kernel U U) (π : Measure U) (m : U → W → ℝ≥0∞) (u_p : U)
    (w : W) : noisyMeaning N π m u_p w = ∑ u_i, N u_i {u_p} * m u_i w * π {u_i} :=
  lintegral_fintype _

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

/-- The listener mass at `w` averaged geometrically over the perceptions of `u_i`: the
exponential of the channel-expected log listener, eq. 7's informativity. -/
noncomputable def channelMix (N : Kernel U U) (L : Kernel U W) (u_i : U) (w : W) : ℝ≥0∞ :=
  ∏ u_p, L u_p {w} ^ (N u_i {u_p}).toReal

/-- The mix over the perceptions the channel can produce. -/
theorem channelMix_eq_prod (N : Kernel U U) (L : Kernel U W) {u_i : U} {s : Finset U}
    (hs : ∀ u_p ∉ s, N u_i {u_p} = 0) (w : W) :
    channelMix N L u_i w = ∏ u_p ∈ s, L u_p {w} ^ (N u_i {u_p}).toReal :=
  (prod_subset (subset_univ s) fun u_p _ hu => by
    rw [hs u_p hu, ENNReal.toReal_zero, ENNReal.rpow_zero]).symm

theorem channelMix_le_one (N : Kernel U U) (L : Kernel U W) {u_i : U} {w : W}
    (hL : ∀ u_p, L u_p {w} ≤ 1) : channelMix N L u_i w ≤ 1 :=
  prod_le_one fun u_p _ => ENNReal.rpow_le_one (hL u_p) ENNReal.toReal_nonneg

variable [MeasurableSingletonClass U]

/-- Without noise the literal listener is the noiseless one at every utterance of positive
finite prior mass. -/
theorem literalListener_noisyMeaning_id (μ : Measure W) (π : Measure U) (m : U → W → ℝ≥0∞)
    {u : U} (h0 : π {u} ≠ 0) (htop : π {u} ≠ ∞) :
    literalListener μ (noisyMeaning Kernel.id π m) u = literalListener μ m u :=
  literalListener_apply_eq_of_eq_mul μ h0 htop (noisyMeaning_id π m u)

theorem channelMix_id (L : Kernel U W) (u : U) (w : W) : channelMix Kernel.id L u w = L u {w} := by
  rw [channelMix_eq_prod _ _ (s := {u}) fun v hv => by
      rw [Kernel.id_apply, Measure.dirac_apply' _ (.singleton v),
        Set.indicator_of_notMem (Set.notMem_singleton_iff.mpr fun h => hv (by simp [h]))],
    prod_singleton, Kernel.id_apply, Measure.dirac_apply_of_mem (Set.mem_singleton u),
    ENNReal.toReal_one, ENNReal.rpow_one]

variable [Countable W] [MeasurableSingletonClass W]

/-- The speaker over the channel (eqs. 4 and 7): power weights of the channel-mixed listener,
scaled by the cost factor of each utterance. -/
noncomputable def noisySpeaker (N : Kernel U U) (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W) :
    Kernel W U :=
  Kernel.ofWeights fun w u => channelMix N L u w ^ α * cost u

@[simp] theorem noisySpeaker_apply_singleton (N : Kernel U U) (α : ℝ) (cost : U → ℝ≥0∞)
    (L : Kernel U W) (w : W) (u : U) :
    noisySpeaker N α cost L w {u} =
      channelMix N L u w ^ α * cost u / ∑ u', channelMix N L u' w ^ α * cost u' :=
  Kernel.ofWeights_apply_singleton _ w u

instance (N : Kernel U U) (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W) :
    IsFiniteKernel (noisySpeaker N α cost L) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights fun w u => channelMix N L u w ^ α * cost u))

/-- Row preference of the speaker reduces to comparing the weighted channel-mixed listener
values; the normalization cancels. -/
theorem noisySpeaker_real_singleton_lt_iff {N : Kernel U U} {α : ℝ} (hα : 0 ≤ α)
    {cost : U → ℝ≥0∞} (hctop : ∀ u, cost u ≠ ∞) {L : Kernel U W} {w : W}
    (hle : ∀ u, L u {w} ≤ 1) (h0 : ∃ u, channelMix N L u w ^ α * cost u ≠ 0) {u u' : U} :
    (noisySpeaker N α cost L w).real {u} < (noisySpeaker N α cost L w).real {u'} ↔
      channelMix N L u w ^ α * cost u < channelMix N L u' w ^ α * cost u' :=
  Kernel.ofWeights_real_singleton_lt_iff w
    (fun h => let ⟨u₀, hu₀⟩ := h0; hu₀ (sum_eq_zero_iff.mp h u₀ (mem_univ _)))
    (ENNReal.sum_ne_top.mpr fun u _ =>
      ENNReal.mul_ne_top (weight_rpow_ne_top hα (channelMix_le_one N L hle)) (hctop u))

/-- Without noise the speaker is the noiseless one. -/
theorem noisySpeaker_id (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W) :
    noisySpeaker Kernel.id α cost L = speaker α cost L := by
  unfold noisySpeaker speaker
  congr 1
  funext w u
  rw [channelMix_id]

end Speaker

/-! ### The pragmatic listener -/

section Listener

variable [MeasurableSingletonClass U] [Countable W] [MeasurableSingletonClass W]
  [StandardBorelSpace W] [Nonempty W] (N : Kernel U U) [IsFiniteKernel N] (α : ℝ)
  (cost : U → ℝ≥0∞) (L : Kernel U W) (μ : Measure W) [IsFiniteMeasure μ]

/-- The pragmatic listener over the channel (eq. 8): the Bayesian inverse, against the prior,
of the speaker followed by the channel. -/
noncomputable def noisyPragmaticListener : Kernel U W := (N ∘ₖ noisySpeaker N α cost L)†μ

instance : IsMarkovKernel (noisyPragmaticListener N α cost L μ) :=
  inferInstanceAs (IsMarkovKernel ((N ∘ₖ noisySpeaker N α cost L)†μ))

/-- Without noise the pragmatic listener is the noiseless one. -/
theorem noisyPragmaticListener_id :
    noisyPragmaticListener Kernel.id α cost L μ = pragmaticListener α cost L μ := by
  simp only [noisyPragmaticListener, noisySpeaker_id, Kernel.id_comp, pragmaticListener]

variable {N α cost L μ}

/-- At a prior giving every state the same positive mass, listener preference between two
states is preference of the channelled speaker between them. -/
theorem noisyPragmaticListener_real_lt_iff (hμeq : ∀ w w', μ {w} = μ {w'})
    (hμ0 : ∀ w, μ {w} ≠ 0) {u : U} {w₀ : W} (hs : (N ∘ₖ noisySpeaker N α cost L) w₀ {u} ≠ 0)
    {w₁ w₂ : W} :
    (noisyPragmaticListener N α cost L μ u).real {w₁} <
        (noisyPragmaticListener N α cost L μ u).real {w₂} ↔
      ((N ∘ₖ noisySpeaker N α cost L) w₁).real {u} <
        ((N ∘ₖ noisySpeaker N α cost L) w₂).real {u} := by
  have hx : ((N ∘ₖ noisySpeaker N α cost L) ∘ₘ μ) {u} ≠ 0 :=
    comp_apply_singleton_ne_zero _ _ (hμ0 w₀) hs
  rw [noisyPragmaticListener, posterior_real_singleton _ _ hx, posterior_real_singleton _ _ hx,
    div_lt_div_iff_of_pos_right
      (by rw [measureReal_def]; exact ENNReal.toReal_pos hx (measure_ne_top _ _)),
    show μ.real {w₁} = μ.real {w₂} by rw [measureReal_def, measureReal_def, hμeq],
    mul_lt_mul_iff_of_pos_left
      (by rw [measureReal_def]; exact ENNReal.toReal_pos (hμ0 w₂) (measure_ne_top _ _))]

end Listener

end RSA
