import Linglib.Pragmatics.RSA.Uniform

/-!
# The exact register for rational-speech-act kernels

This file computes the kernels of `Linglib.Pragmatics.RSA.Basic` in `ℚ≥0`. At a natural
rationality, rational listener rows and rational cost factors give rational speaker rows
(`RSA.speaker_nnratCast_apply_singleton`) and `RSA.share` is the rational normalization; the
uniform literal listener has rational rows
(`RSA.uniformListener_nnratCast_apply_singleton`); and against a uniform prior the rows of the
pragmatic listener and of the family listener are the rational shares of the speaker's column
(`RSA.pragmaticListener_uniformOn_nnratCast_apply_singleton`,
`RSA.familyListener_uniformOn_nnratCast_apply_singleton`, with the state and latent marginals).
A study states its tower twice, as kernels and as rational functions, connects the two level by
level with these lemmas, and closes each prediction by kernel reduction on the rational face,
transported to the real face by `ENNReal.toReal_nnratCast`. The costless uniform model has the
ℕ-valued register of `Linglib.Pragmatics.RSA.Uniform` instead.

## References

* [potts-levy-2015]
* [potts-etal-2016]
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNRat

namespace RSA

/-- The share of `x` in a rational weight function: its weight over the total. -/
def share {σ : Type*} [Fintype σ] (f : σ → ℚ≥0) (x : σ) : ℚ≥0 := f x / ∑ y, f y

section Uniform

variable {T C : Type*} [Fintype T] [DecidableEq T] [MeasurableSpace T]
  [DiscreteMeasurableSpace T] [Fintype C] [MeasurableSpace C] [DiscreteMeasurableSpace C]
  (sem : C → Finset T)

/-- The uniform literal listener has rational rows: the reciprocal of the extension's size. -/
theorem uniformListener_nnratCast_apply_singleton (c : C) (t : T) :
    uniformListener sem c {t}
      = ((if t ∈ sem c then ((sem c).card : ℚ≥0)⁻¹ else 0 : ℚ≥0) : ℝ≥0∞) := by
  rw [uniformListener_apply_singleton]
  split_ifs with h
  · rw [ENNReal.nnratCast_inv _ (by exact_mod_cast (Finset.card_pos.2 ⟨t, h⟩).ne'),
      ENNReal.nnratCast_natCast]
  · rw [ENNReal.nnratCast_zero]

end Uniform

variable {W U : Type*} [MeasurableSpace W] [MeasurableSpace U] [Countable W]
  [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U]

/-- At a natural rationality, a speaker over rational listener rows and rational cost factors
has rational rows: the weighted share of the utterance in the state's row. -/
theorem speaker_nnratCast_apply_singleton {α : ℝ} {k : ℕ} (hα : α = k) {cost : U → ℝ≥0∞}
    {c : U → ℚ≥0} (hcost : ∀ u, cost u = c u) {L : Kernel U W} {q : U → W → ℚ≥0}
    (hL : ∀ u w, L u {w} = q u w) {w : W} (hw : ∑ u, q u w ^ k * c u ≠ 0) (u : U) :
    speaker α cost L w {u} = ((q u w ^ k * c u / ∑ u', q u' w ^ k * c u' : ℚ≥0) : ℝ≥0∞) := by
  have hweight : (fun w u => L u {w} ^ α * cost u)
      = fun w u => ((q u w ^ k * c u : ℚ≥0) : ℝ≥0∞) := by
    funext w u
    rw [hL, hcost, hα, ENNReal.rpow_natCast, ENNReal.nnratCast_mul, ENNReal.nnratCast_pow]
  rw [speaker, hweight]
  exact Kernel.ofWeights_nnratCast_apply_singleton _ w hw u

/-- The speaker at rationality one: the cost-weighted share of the utterance in the row. -/
theorem speaker_one_nnratCast_apply_singleton {cost : U → ℝ≥0∞} {c : U → ℚ≥0}
    (hcost : ∀ u, cost u = c u) {L : Kernel U W} {q : U → W → ℚ≥0} (hL : ∀ u w, L u {w} = q u w)
    {w : W} (hw : ∑ u, q u w * c u ≠ 0) (u : U) :
    speaker 1 cost L w {u} = ((q u w * c u / ∑ u', q u' w * c u' : ℚ≥0) : ℝ≥0∞) := by
  simpa only [pow_one] using speaker_nnratCast_apply_singleton (k := 1) Nat.cast_one.symm hcost hL
    (by simpa only [pow_one] using hw) u

section Listener

variable [StandardBorelSpace W] [Nonempty W] [Fintype W]

/-- Against the uniform prior, the pragmatic listener of a speaker with rational rows has
rational rows: the state's share of the utterance's column. -/
theorem pragmaticListener_uniformOn_nnratCast_apply_singleton (α : ℝ) (cost : U → ℝ≥0∞)
    (L : Kernel U W) {s : W → U → ℚ≥0} (hs : ∀ w u, speaker α cost L w {u} = s w u) {u : U}
    (hu : ∑ w, s w u ≠ 0) (w : W) :
    pragmaticListener α cost L (uniformOn Set.univ) u {w}
      = ((s w u / ∑ w', s w' u : ℚ≥0) : ℝ≥0∞) :=
  posterior_uniformOn_univ_nnratCast_apply_singleton _ s hs hu w

variable {Λ : Type*} [MeasurableSpace Λ] [Countable Λ] [MeasurableSingletonClass Λ]
  [StandardBorelSpace Λ] [Nonempty Λ] [Fintype Λ] (L : Λ → Kernel U W) (α : ℝ)
  (cost : U → ℝ≥0∞) {s : W × Λ → U → ℚ≥0} (hs : ∀ p u, speaker α cost (L p.2) p.1 {u} = s p u)
  {u : U} (hu : ∑ p, s p u ≠ 0)

include hs hu

/-- Against the uniform prior on pairs, the family listener of member speakers with rational
rows has rational rows: the pair's share of the utterance's column. -/
theorem familyListener_uniformOn_nnratCast_apply_singleton (p : W × Λ) :
    familyListener L α cost (uniformOn Set.univ) u {p}
      = ((s p u / ∑ p', s p' u : ℚ≥0) : ℝ≥0∞) := by
  rw [familyListener]
  exact posterior_uniformOn_univ_nnratCast_apply_singleton _ s
    (λ p u => by rw [familySpeaker_apply, hs]) hu p

/-- The state marginal of the family listener, pooling the latents. -/
theorem familyListener_uniformOn_nnratCast_fst_apply_singleton (w : W) :
    (familyListener L α cost (uniformOn Set.univ) u).fst {w}
      = ((∑ l, s (w, l) u / ∑ p', s p' u : ℚ≥0) : ℝ≥0∞) := by
  rw [Measure.fst_apply_singleton, ENNReal.nnratCast_sum]
  exact Finset.sum_congr rfl λ l _ =>
    familyListener_uniformOn_nnratCast_apply_singleton L α cost hs hu (w, l)

/-- The latent marginal of the family listener, pooling the states. -/
theorem familyListener_uniformOn_nnratCast_snd_apply_singleton (l : Λ) :
    (familyListener L α cost (uniformOn Set.univ) u).snd {l}
      = ((∑ w, s (w, l) u / ∑ p', s p' u : ℚ≥0) : ℝ≥0∞) := by
  rw [Measure.snd_apply_singleton, ENNReal.nnratCast_sum]
  exact Finset.sum_congr rfl λ w _ =>
    familyListener_uniformOn_nnratCast_apply_singleton L α cost hs hu (w, l)

end Listener

end RSA
