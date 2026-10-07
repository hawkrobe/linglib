module

public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Linglib.Core.MeasureTheory.Measure.WithDensity
public import Linglib.Core.Probability.GibbsVariational
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Core.Probability.Kernel.Posterior
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# The Rational Speech Act pipeline on probability kernels

This file defines the Rational Speech Act model in mathlib's probability vocabulary, following
Frank and Goodman's model as presented in Degen's review (eqs. 1–4) and in Franke and Bergen's
comparison of latent-variable variants (eqs. 5–22). The literal listener is the prior
reweighted by a graded meaning, the speaker is the best response in power-weight form
(`ENNReal.rpow` is total, so falsity needs no signed utilities), and the pragmatic listeners
are mathlib's posterior kernels `κ†μ`, of the speaker, or of the deterministic observation
kernel over the joint of prior and speaker when the listener hears only the form of the
speaker's choice. Rationality, cost, meaning, and prior are arguments, so findings quantify
over them. The uniform-prior Boolean specialization with its decision procedure is
`Linglib.Pragmatics.RSA.Uniform`.

## Main definitions

* `RSA.literalListener` — eq. 1: the prior reweighted by the meaning.
* `RSA.speaker` — eqs. 2/6–7: `ProbabilityTheory.Kernel.ofWeights` of `L ^ α · cost`.
* `RSA.speakerOfScore` — the softmax of an extended-real utility, `⊥` marking the
  inapplicable utterances; `RSA.speaker` is its instance at the informativity utility
  (`RSA.speaker_eq_speakerOfScore`).
* `RSA.pragmaticListener` — eq. 3: `(speaker α cost L)†μ`.
* `RSA.priorOfWeights` — the prior determined by integer weights on the states.
* `RSA.jointListener` — eqs. 18b/21b: the posterior over (state, choice) given the heard
  form; `.fst` is the state listener, `.snd` the choice posterior.
* `RSA.familySpeaker`, `RSA.familyListener` — state-side latents (eqs. 11–13): the latent
  is a speaker argument and normalization is per latent.

## Main results

* `RSA.speaker_literalListener_indicator_real_singleton_lt_iff` — with Boolean meanings a
  state prefers the utterance with the smaller extension.
* `RSA.speaker_literalListener_indicator_congr`,
  `RSA.speaker_literalListener_indicator_le_of_subset` — with Boolean meanings the speaker sees a
  state only through the utterances true at it, and produces each of them less the more there are.
* `RSA.jointListener_apply_singleton` — exact Bayes for the joint listener.
* `RSA.speakerOfScore_eq_tilted`, `RSA.isGreatest_freeEnergy_speakerOfScore` — a score-speaker
  row is the Gibbs measure of its score over the applicable utterances, and so the rational
  optimizer: it maximizes the expected score less the divergence from the uniform measure on
  them (the Gibbs variational principle).
* `RSA.tendsto_speaker_real_singleton_atTop` — as rationality grows the speaker puts all its mass
  on the utterance the listener most favors.
* `RSA.jointListener_fst_real_lt_iff`, `RSA.jointListener_snd_real_lt_iff`,
  `RSA.familyListener_fst_real_lt_iff`, `RSA.familyListener_snd_real_lt_iff` — listener
  preference as prior-weighted speaker sums.

## References

* [M. C. Frank and N. D. Goodman, *Predicting Pragmatic Reasoning in Language Games*
  (2012)][frank-goodman-2012]
* [J. Degen, *The Rational Speech Act Framework* (2023)][degen-2023]
* [M. Franke and L. Bergen, *Theory-Driven Statistical Modeling for Semantics and Pragmatics: A
  Case Study on Grammatically Generated Implicature Readings* (2020)][franke-bergen-2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### The RSA pipeline -/

namespace RSA

section Pipeline

variable {W U O : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSpace O]

section LiteralListener

variable [Countable U] [MeasurableSingletonClass U]

/-- The literal listener (eq. 1) is the prior reweighted by the graded meaning of the utterance and
renormalized. -/
noncomputable def literalListener (μ : Measure W) (m : U → W → ℝ≥0∞) : Kernel U W :=
  Kernel.ofFunOfCountable fun u ↦ (μ.withDensity (m u))[|Set.univ]

theorem literalListener_apply (μ : Measure W) (m : U → W → ℝ≥0∞) (u : U) :
    literalListener μ m u = (μ.withDensity (m u))[|Set.univ] := rfl

/-- The literal listener is a subprobability at every event. -/
theorem literalListener_apply_le_one (μ : Measure W) (m : U → W → ℝ≥0∞) (u : U) (s : Set W) :
    literalListener μ m u s ≤ 1 := by
  rw [literalListener_apply, cond_apply MeasurableSet.univ, Set.univ_inter]
  rcases eq_or_ne (μ.withDensity (m u) Set.univ) 0 with h | h
  · rw [measure_mono_null (Set.subset_univ s) h, mul_zero]
    exact zero_le_one
  · calc (μ.withDensity (m u) Set.univ)⁻¹ * μ.withDensity (m u) s
        ≤ (μ.withDensity (m u) Set.univ)⁻¹ * μ.withDensity (m u) Set.univ :=
          mul_le_mul' le_rfl (measure_mono (Set.subset_univ s))
      _ ≤ 1 := ENNReal.inv_mul_le_one _

/-- The literal listener at an utterance depends on that utterance's meaning only up to a
positive finite scalar, which the normalization absorbs. -/
theorem literalListener_apply_eq_of_eq_mul (μ : Measure W) {m m' : U → W → ℝ≥0∞} {u : U}
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (h : ∀ w, m' u w = c * m u w) :
    literalListener μ m' u = literalListener μ m u := by
  rw [literalListener_apply, literalListener_apply,
    show μ.withDensity (m' u) = c • μ.withDensity (m u) by
      rw [show m' u = fun w ↦ c * m u w from funext h]; exact withDensity_smul' c (m u) hc]
  ext s hs
  rw [cond_apply MeasurableSet.univ, cond_apply MeasurableSet.univ, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hc),
    mul_mul_mul_comm, ENNReal.inv_mul_cancel hc0 hc, one_mul]

/-- The literal listener depends on the meaning only up to a positive finite scalar. -/
theorem literalListener_const_mul (μ : Measure W) (m : U → W → ℝ≥0∞) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ∞) : literalListener μ (fun u w ↦ c * m u w) = literalListener μ m :=
  Kernel.ext fun _ ↦ literalListener_apply_eq_of_eq_mul μ hc0 hc fun _ ↦ rfl

/-- Every finite measure on a countable discrete space is a literal listener at a prior of
positive mass everywhere, with the measure's density against the prior as the meaning. -/
theorem literalListener_div [Countable W] [MeasurableSingletonClass W] (μ : Measure W)
    [IsFiniteMeasure μ] (hμ : ∀ w, μ {w} ≠ 0) (ν : U → Measure W) (u : U) :
    literalListener μ (fun u w ↦ ν u {w} / μ {w}) u = (ν u)[|Set.univ] := by
  rw [literalListener_apply]
  congr 1
  refine Measure.ext_of_singleton fun w ↦ ?_
  rw [withDensity_apply _ (.singleton w), lintegral_singleton,
    ENNReal.div_mul_cancel (hμ w) (measure_ne_top μ _)]

/-- On a Boolean meaning the literal listener conditions the prior on the extension. -/
theorem literalListener_indicator [DiscreteMeasurableSpace W] (μ : Measure W)
    (sem : U → Set W) :
    literalListener μ (fun u ↦ (sem u).indicator 1) = Kernel.ofFunOfCountable fun u ↦ μ[|sem u] :=
  Kernel.ext fun u ↦ by
    show (μ.withDensity ((sem u).indicator 1))[|Set.univ] = μ[|sem u]
    rw [withDensity_indicator_one .of_discrete]
    simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.restrict_apply_univ]

theorem literalListener_apply_singleton' [MeasurableSingletonClass W] (μ : Measure W)
    (m : U → W → ℝ≥0∞) (u : U) (w : W) :
    literalListener μ m u {w} = m u w * μ {w} / ∫⁻ w', m u w' ∂μ := by
  rw [literalListener_apply, cond_apply MeasurableSet.univ, Set.univ_inter,
    withDensity_apply _ (.singleton w), lintegral_singleton, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ENNReal.div_eq_inv_mul]

theorem literalListener_apply_singleton [Fintype W] [MeasurableSingletonClass W] (μ : Measure W)
    (m : U → W → ℝ≥0∞) (u : U) (w : W) :
    literalListener μ m u {w} = m u w * μ {w} / ∑ w', m u w' * μ {w'} := by
  rw [literalListener_apply_singleton', lintegral_fintype]

/-- A relabelling of the states that carries one prior and meaning to another carries the literal
listener along. -/
theorem literalListener_apply_singleton_of_equiv {W' U' : Type*} [MeasurableSpace W']
    [MeasurableSpace U'] [Countable U'] [MeasurableSingletonClass U'] [Fintype W]
    [MeasurableSingletonClass W] [Fintype W'] [MeasurableSingletonClass W'] (e : W ≃ W')
    {μ : Measure W} {μ' : Measure W'} {m : U → W → ℝ≥0∞} {m' : U' → W' → ℝ≥0∞} {u : U} {u' : U'}
    (hμ : ∀ w, μ' {e w} = μ {w}) (hm : ∀ w, m' u' (e w) = m u w) (w : W) :
    literalListener μ' m' u' {e w} = literalListener μ m u {w} := by
  rw [literalListener_apply_singleton, literalListener_apply_singleton, hm, hμ, ← e.sum_comp]
  simp only [hm, hμ]

/-- The literal listener of an utterance whose meaning has positive finite mass under the prior is
a probability measure. -/
theorem isProbabilityMeasure_literalListener (μ : Measure W) (m : U → W → ℝ≥0∞) (u : U)
    (h0 : ∫⁻ w, m u w ∂μ ≠ 0) (htop : ∫⁻ w, m u w ∂μ ≠ ∞) :
    IsProbabilityMeasure (literalListener μ m u) := by
  rw [literalListener_apply]
  refine cond_isProbabilityMeasure_of_finite ?_ ?_ <;>
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- Marginalizing a joint literal listener whose meaning depends on the first coordinate alone
gives the literal listener on the marginal prior, since the meaning carries no information about
the second coordinate. -/
theorem literalListener_map_fst {V : Type*} [MeasurableSpace V] (μ : Measure (W × V))
    (m : U → W → ℝ≥0∞) (hm : ∀ u, Measurable (m u)) (u : U) :
    (literalListener μ (fun u p ↦ m u p.1) u).map Prod.fst =
      literalListener (μ.map Prod.fst) m u := by
  have key : (μ.withDensity fun p ↦ m u p.1).map Prod.fst = (μ.map Prod.fst).withDensity (m u) :=
    Measure.map_withDensity_comp (hm u) measurable_fst
  have huniv : (μ.withDensity fun p ↦ m u p.1) Set.univ =
      (μ.map Prod.fst).withDensity (m u) Set.univ := by
    rw [← key, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  simp only [literalListener_apply, ProbabilityTheory.cond, Measure.restrict_univ,
    Measure.map_smul _ measurable_fst.aemeasurable, key, huniv]

theorem literalListener_indicator_apply_singleton [DiscreteMeasurableSpace W] (μ : Measure W)
    (sem : U → Set W) {u : U} {w : W} (h : w ∈ sem u) :
    literalListener μ (fun u ↦ (sem u).indicator 1) u {w} = (μ (sem u))⁻¹ * μ {w} := by
  rw [literalListener_indicator, Kernel.ofFunOfCountable_apply, cond_apply .of_discrete,
    Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)]

theorem literalListener_indicator_apply_singleton_of_notMem [DiscreteMeasurableSpace W]
    (μ : Measure W) (sem : U → Set W) {u : U} {w : W} (h : w ∉ sem u) :
    literalListener μ (fun u ↦ (sem u).indicator 1) u {w} = 0 := by
  rw [literalListener_indicator, Kernel.ofFunOfCountable_apply, cond_apply .of_discrete,
    Set.inter_comm, Set.singleton_inter_eq_empty.mpr h, measure_empty, mul_zero]

/-- A tautology leaves a probability prior unchanged. -/
theorem literalListener_indicator_apply_singleton_of_eq_univ [DiscreteMeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] (sem : U → Set W) {u : U} (h : sem u = Set.univ)
    (w : W) : literalListener μ (fun u ↦ (sem u).indicator 1) u {w} = μ {w} := by
  rw [literalListener_indicator_apply_singleton μ sem (by rw [h]; exact Set.mem_univ w), h,
    measure_univ, inv_one, one_mul]

/-- An utterance true at one state only puts all its mass there. -/
theorem literalListener_indicator_apply_singleton_of_eq_singleton [DiscreteMeasurableSpace W]
    (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) {u : U} {w : W} (h : sem u = {w})
    (hμ : μ {w} ≠ 0) : literalListener μ (fun u ↦ (sem u).indicator 1) u {w} = 1 := by
  rw [literalListener_indicator_apply_singleton μ sem (by rw [h]; exact Set.mem_singleton w), h,
    ENNReal.inv_mul_cancel hμ (measure_ne_top _ _)]

/-- The literal listener of an utterance with a positive-mass extension is a probability
measure. -/
theorem literalListener_indicator_apply_univ [DiscreteMeasurableSpace W] (μ : Measure W)
    [IsFiniteMeasure μ] (sem : U → Set W) {u : U} (h : μ (sem u) ≠ 0) :
    literalListener μ (fun u ↦ (sem u).indicator 1) u Set.univ = 1 := by
  rw [literalListener_indicator, Kernel.ofFunOfCountable_apply]
  have := cond_isProbabilityMeasure h
  exact measure_univ

/-- On a finite-mass extension the literal listener is a subprobability at members. -/
theorem literalListener_indicator_apply_singleton_le_one [DiscreteMeasurableSpace W]
    (μ : Measure W) (sem : U → Set W) {u : U} (hfin : μ (sem u) ≠ ∞) {w : W} (h : w ∈ sem u) :
    literalListener μ (fun u ↦ (sem u).indicator 1) u {w} ≤ 1 := by
  rw [literalListener_indicator_apply_singleton μ sem h]
  rcases eq_or_ne (μ (sem u)) 0 with h0 | h0
  · rw [measure_mono_null (Set.singleton_subset_iff.mpr h) h0, mul_zero]
    exact zero_le_one
  · rw [ENNReal.inv_mul_le_iff h0 hfin, mul_one]
    exact measure_mono (Set.singleton_subset_iff.mpr h)

/-- With Boolean meanings the literal listener puts mass on a state exactly when the utterance
is true there and the state has positive prior. -/
theorem literalListener_indicator_apply_singleton_ne_zero_iff [DiscreteMeasurableSpace W]
    (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) (u : U) (w : W) :
    literalListener μ (fun u ↦ (sem u).indicator 1) u {w} ≠ 0 ↔ w ∈ sem u ∧ μ {w} ≠ 0 := by
  by_cases h : w ∈ sem u
  · rw [literalListener_indicator_apply_singleton μ sem h]
    exact ⟨fun h' ↦ ⟨h, (mul_ne_zero_iff.mp h').2⟩,
      fun h' ↦ mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) h'.2⟩
  · rw [literalListener_indicator_apply_singleton_of_notMem μ sem h]
    exact iff_of_false (fun h' ↦ h' rfl) fun h' ↦ h h'.1

/-- The prior determined by natural-number weights on the states. Only the ratios matter to
the pipeline, so a paper's table of percentages is recorded as integer weights. -/
noncomputable def priorOfWeights [Fintype W] (w : W → ℕ) : Measure W :=
  ∑ x, (w x : ℝ≥0∞) • Measure.dirac x

section PriorOfWeights

variable [Fintype W] [MeasurableSingletonClass W] (w : W → ℕ)

@[simp] theorem priorOfWeights_singleton (x : W) : priorOfWeights w {x} = w x :=
  Measure.sum_smul_dirac_apply_singleton (fun x ↦ (w x : ℝ≥0∞)) x

instance : IsFiniteMeasure (priorOfWeights w) :=
  ⟨by
    rw [priorOfWeights, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun x _ ↦ by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact ENNReal.natCast_lt_top _⟩

theorem priorOfWeights_singleton_ne_zero {x : W} (h : w x ≠ 0) : priorOfWeights w {x} ≠ 0 := by
  rw [priorOfWeights_singleton]
  exact_mod_cast h

/-- The mass of a finite set under the weight prior is the sum of its weights. -/
theorem priorOfWeights_apply_finset (s : Finset W) :
    priorOfWeights w ↑s = ∑ x ∈ s, (w x : ℝ≥0∞) := by
  rw [← sum_measure_singleton]
  simp only [priorOfWeights_singleton]

/-- On natural-number weights and likelihoods the literal listener is the weighted likelihood
over its total. -/
theorem literalListener_natCast_real_singleton (lik : U → W → ℕ) (u : U) (x : W) :
    (literalListener (priorOfWeights w) (fun u x ↦ (lik u x : ℝ≥0∞)) u).real {x}
      = (lik u x * w x : ℝ) / ∑ x', (lik u x' * w x' : ℝ) := by
  rw [measureReal_def, literalListener_apply_singleton, ENNReal.toReal_div,
    ENNReal.toReal_sum fun _ _ ↦ ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)]
  simp [ENNReal.toReal_mul]

end PriorOfWeights

end LiteralListener

variable [Countable W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U]

theorem weight_rpow_ne_zero {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hx : x ≠ 0) :
    x ^ α ≠ 0 := by
  rw [ne_eq, ENNReal.rpow_eq_zero_iff, not_or]
  exact ⟨fun h ↦ hx h.1, fun h ↦ absurd hα (not_le.mpr h.2)⟩

theorem weight_rpow_ne_top {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hle : x ≤ 1) :
    x ^ α ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (ENNReal.one_rpow α ▸ ENNReal.rpow_le_rpow hle hα)

/-- The pragmatic speaker (eqs. 2/6–7) is the best response to a listener kernel, with power weights
`L u {w} ^ α` scaled by the cost factor of each utterance. -/
noncomputable def speaker (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W) : Kernel W U :=
  Kernel.ofWeights fun w u ↦ L u {w} ^ α * cost u

@[simp] theorem speaker_apply_singleton (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W) (w : W)
    (u : U) :
    speaker α cost L w {u} = L u {w} ^ α * cost u / ∑ u', L u' {w} ^ α * cost u' :=
  Kernel.ofWeights_apply_singleton _ w u

/-- Relabelling the utterances carries the speaker along, with the cost relabelled with them. A
listener that treats `τ v` at `w'` as the other treats `v` at `w` makes the speaker at `w'` produce
`τ u` as the other produces `u` at `w`. -/
theorem speaker_apply_singleton_of_equiv {W' U' : Type*} [MeasurableSpace W'] [MeasurableSpace U']
    [Countable W'] [MeasurableSingletonClass W'] [Fintype U'] [MeasurableSingletonClass U']
    (τ : U ≃ U') (α : ℝ) (cost : U' → ℝ≥0∞) {L : Kernel U W} {L' : Kernel U' W'} {w : W}
    {w' : W'} (h : ∀ v, L' (τ v) {w'} = L v {w}) (u : U) :
    speaker α cost L' w' {τ u} = speaker α (cost ∘ τ) L w {u} := by
  rw [speaker_apply_singleton, speaker_apply_singleton, h, ← τ.sum_comp]
  simp only [h, Function.comp_apply]

instance (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W) : IsFiniteKernel (speaker α cost L) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

omit [MeasurableSingletonClass U] in
/-- The speaker is a probability kernel whenever every state has a true utterance and the
cost factors are positive and finite. -/
theorem isMarkovKernel_speaker {α : ℝ} (hα : 0 ≤ α) {cost : U → ℝ≥0∞}
    (hc0 : ∀ u, cost u ≠ 0) (hctop : ∀ u, cost u ≠ ∞) (L : Kernel U W)
    (hle : ∀ u w, L u {w} ≤ 1) (h0 : ∀ w, ∃ u, L u {w} ≠ 0) :
    IsMarkovKernel (speaker α cost L) :=
  Kernel.isMarkovKernel_ofWeights
    (fun w ↦ (h0 w).imp fun u hu ↦ mul_ne_zero (weight_rpow_ne_zero hα hu) (hc0 u))
    fun w u ↦ ENNReal.mul_ne_top (weight_rpow_ne_top hα (hle u w)) (hctop u)

/-- A literally false utterance is never produced (positive rationality). -/
theorem speaker_apply_singleton_eq_zero {α : ℝ} (hα : 0 < α) {cost : U → ℝ≥0∞}
    {L : Kernel U W} {w : W} {u : U} (h : L u {w} = 0) : speaker α cost L w {u} = 0 := by
  rw [speaker_apply_singleton, h, ENNReal.zero_rpow_of_pos hα, zero_mul, ENNReal.zero_div]

/-- A literally true utterance is produced with positive mass. -/
theorem speaker_apply_singleton_ne_zero {α : ℝ} (hα : 0 ≤ α) {cost : U → ℝ≥0∞}
    (hc0 : ∀ u, cost u ≠ 0) (hctop : ∀ u, cost u ≠ ∞) {L : Kernel U W} {w : W}
    (hle : ∀ u', L u' {w} ≤ 1) {u : U} (h : L u {w} ≠ 0) : speaker α cost L w {u} ≠ 0 :=
  Kernel.ofWeights_apply_singleton_ne_zero (mul_ne_zero (weight_rpow_ne_zero hα h) (hc0 u))
    fun u' ↦ ENNReal.mul_ne_top (weight_rpow_ne_top hα (hle u')) (hctop u')

/-- A state with a unique applicable utterance produces it with certainty. -/
theorem speaker_apply_singleton_eq_one {α : ℝ} (hα : 0 < α) {cost : U → ℝ≥0∞} {u : U}
    (hc0 : cost u ≠ 0) (hctop : cost u ≠ ∞) {L : Kernel U W} {w : W} (h : L u {w} ≠ 0)
    (hle : L u {w} ≤ 1) (hother : ∀ u' ≠ u, L u' {w} = 0) : speaker α cost L w {u} = 1 := by
  rw [speaker_apply_singleton, Finset.sum_eq_single u
    (fun u' _ hu' ↦ by rw [hother u' hu', ENNReal.zero_rpow_of_pos hα, zero_mul])
    (fun hu ↦ absurd (Finset.mem_univ u) hu)]
  exact ENNReal.div_self (mul_ne_zero (weight_rpow_ne_zero hα.le h) hc0)
    (ENNReal.mul_ne_top (weight_rpow_ne_top hα.le hle) hctop)

/-- On reals a speaker share is the weighted listener value over the row's total. -/
theorem speaker_real_singleton {α : ℝ} (hα : 0 ≤ α) {cost : U → ℝ≥0∞} (hctop : ∀ u, cost u ≠ ∞)
    {L : Kernel U W} {w : W} (hle : ∀ u, L u {w} ≤ 1) (u : U) :
    (speaker α cost L w).real {u}
      = (L u {w} ^ α).toReal * (cost u).toReal
        / ∑ u', (L u' {w} ^ α).toReal * (cost u').toReal := by
  rw [measureReal_def, speaker_apply_singleton, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_sum fun u' _ ↦ ENNReal.mul_ne_top (weight_rpow_ne_top hα (hle u')) (hctop u')]
  simp_rw [ENNReal.toReal_mul]

omit [MeasurableSingletonClass U] in
/-- Speaker shares are at most one. -/
theorem speaker_real_singleton_le_one (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W) (w : W)
    (u : U) : (speaker α cost L w).real {u} ≤ 1 := by
  rw [measureReal_def, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    ((measure_mono (Set.subset_univ _)).trans (Kernel.ofWeights_apply_univ_le_one _ w))

/-- With Boolean meanings, a state whose only true utterance is `u` produces `u` with
certainty at any prior giving the state positive mass. -/
theorem speaker_literalListener_indicator_eq_one [DiscreteMeasurableSpace W] {α : ℝ}
    (hα : 0 < α) {cost : U → ℝ≥0∞} {u : U} (hc0 : cost u ≠ 0) (hctop : cost u ≠ ∞)
    (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) {w : W} (hμ : μ {w} ≠ 0)
    (hmem : w ∈ sem u) (hother : ∀ u' ≠ u, w ∉ sem u') :
    speaker α cost (literalListener μ fun u ↦ (sem u).indicator 1) w {u} = 1 :=
  speaker_apply_singleton_eq_one hα hc0 hctop
    (by
      rw [literalListener_indicator_apply_singleton μ sem hmem]
      exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hμ)
    (literalListener_indicator_apply_singleton_le_one μ sem (measure_ne_top _ _) hmem)
    fun u' hu' ↦ literalListener_indicator_apply_singleton_of_notMem μ sem (hother u' hu')

/-- With Boolean meanings the speaker produces an utterance at a state exactly when it is true
there and the state has positive prior. -/
theorem speaker_literalListener_indicator_apply_singleton_ne_zero_iff
    [DiscreteMeasurableSpace W] {α : ℝ} (hα : 0 < α) {cost : U → ℝ≥0∞} (hc0 : ∀ u, cost u ≠ 0)
    (hctop : ∀ u, cost u ≠ ∞) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) (u : U)
    (w : W) :
    speaker α cost (literalListener μ fun u ↦ (sem u).indicator 1) w {u} ≠ 0
      ↔ w ∈ sem u ∧ μ {w} ≠ 0 := by
  rw [← literalListener_indicator_apply_singleton_ne_zero_iff μ sem u w]
  exact ⟨fun h h' ↦ h (speaker_apply_singleton_eq_zero hα h'),
    speaker_apply_singleton_ne_zero hα.le hc0 hctop
      fun u' ↦ literalListener_apply_le_one μ _ u' {w}⟩

/-- With Boolean meanings the speaker sees a state only through the utterances true at it, so two
states of positive prior verifying the same utterances have the same production row. -/
theorem speaker_literalListener_indicator_congr [DiscreteMeasurableSpace W] {α : ℝ}
    (hα : 0 < α) (cost : U → ℝ≥0∞) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W)
    {w w' : W} (hw : μ {w} ≠ 0) (hw' : μ {w'} ≠ 0) (h : ∀ u, w ∈ sem u ↔ w' ∈ sem u) :
    speaker α cost (literalListener μ fun u ↦ (sem u).indicator 1) w'
      = speaker α cost (literalListener μ fun u ↦ (sem u).indicator 1) w := by
  refine Kernel.ofWeights_apply_eq_of_mul (c := (μ {w'} / μ {w}) ^ α)
    (weight_rpow_ne_zero hα.le (ENNReal.div_ne_zero.mpr ⟨hw', measure_ne_top _ _⟩))
    (ENNReal.rpow_ne_top_of_nonneg hα.le (ENNReal.div_ne_top (measure_ne_top _ _) hw))
    fun u ↦ ?_
  by_cases hu : w ∈ sem u
  · rw [literalListener_indicator_apply_singleton μ sem hu,
      literalListener_indicator_apply_singleton μ sem ((h u).mp hu), mul_right_comm,
      ← ENNReal.mul_rpow_of_nonneg _ _ hα.le, mul_assoc,
      ENNReal.mul_div_cancel hw (measure_ne_top _ _)]
  · rw [literalListener_indicator_apply_singleton_of_notMem μ sem hu,
      literalListener_indicator_apply_singleton_of_notMem μ sem (mt (h u).mpr hu),
      ENNReal.zero_rpow_of_pos hα, zero_mul, zero_mul]

/-- With Boolean meanings the prior cancels from the speaker, which at a state of positive prior
weights each true utterance by its extension's mass to the power `-α` and by its cost. -/
theorem speaker_literalListener_indicator_apply_singleton [DiscreteMeasurableSpace W] {α : ℝ}
    (hα : 0 < α) (cost : U → ℝ≥0∞) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W)
    {w : W} (hw : μ {w} ≠ 0) (u : U) :
    speaker α cost (literalListener μ fun u ↦ (sem u).indicator 1) w {u}
      = (sem u).indicator (fun _ ↦ (μ (sem u))⁻¹ ^ α * cost u) w
        / ∑ u', (sem u').indicator (fun _ ↦ (μ (sem u'))⁻¹ ^ α * cost u') w := by
  have key : ∀ v, (literalListener μ fun u ↦ (sem u).indicator 1) v {w} ^ α * cost v
      = μ {w} ^ α * (sem v).indicator (fun _ ↦ (μ (sem v))⁻¹ ^ α * cost v) w := fun v ↦ by
    by_cases hv : w ∈ sem v
    · rw [literalListener_indicator_apply_singleton μ sem hv, Set.indicator_of_mem hv,
        ENNReal.mul_rpow_of_nonneg _ _ hα.le]
      ring
    · rw [literalListener_indicator_apply_singleton_of_notMem μ sem hv,
        Set.indicator_of_notMem hv, ENNReal.zero_rpow_of_pos hα, zero_mul, mul_zero]
  rw [speaker_apply_singleton, key, Finset.sum_congr rfl fun v _ ↦ key v, ← Finset.mul_sum,
    ENNReal.mul_div_mul_left _ _ (weight_rpow_ne_zero hα.le hw)
      (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))]

/-- With Boolean meanings a state verifying more utterances produces each of its true utterances
less, since the prior cancels from the speaker and only the inclusion of the true utterances
matters. -/
theorem speaker_literalListener_indicator_le_of_subset [DiscreteMeasurableSpace W] {α : ℝ}
    (hα : 0 < α) (cost : U → ℝ≥0∞) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W)
    {w w' : W} (hw : μ {w} ≠ 0) (hsub : ∀ u, w ∈ sem u → w' ∈ sem u) {u : U} (hu : w ∈ sem u) :
    speaker α cost (literalListener μ fun u ↦ (sem u).indicator 1) w' {u}
      ≤ speaker α cost (literalListener μ fun u ↦ (sem u).indicator 1) w {u} := by
  rcases eq_or_ne (μ {w'}) 0 with hw' | hw'
  · rw [speaker_apply_singleton_eq_zero hα (not_not.mp fun h ↦
      ((literalListener_indicator_apply_singleton_ne_zero_iff μ sem u w').mp h).2 hw')]
    exact zero_le
  rw [speaker_literalListener_indicator_apply_singleton hα cost μ sem hw,
    speaker_literalListener_indicator_apply_singleton hα cost μ sem hw',
    Set.indicator_of_mem hu, Set.indicator_of_mem (hsub u hu)]
  refine ENNReal.div_le_div_left (Finset.sum_le_sum fun v _ ↦ ?_) _
  by_cases hv : w ∈ sem v
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hsub v hv)]
  · rw [Set.indicator_of_notMem hv]; exact zero_le

/-- Row-preference of the speaker reduces to comparing the weighted listener values; the
normalization cancels. -/
theorem speaker_real_singleton_lt_iff {α : ℝ} (hα : 0 ≤ α) {cost : U → ℝ≥0∞}
    (hctop : ∀ u, cost u ≠ ∞) {L : Kernel U W} {w : W} (hle : ∀ u, L u {w} ≤ 1)
    (h0 : ∃ u, L u {w} ^ α * cost u ≠ 0) {u u' : U} :
    (speaker α cost L w).real {u} < (speaker α cost L w).real {u'} ↔
      L u {w} ^ α * cost u < L u' {w} ^ α * cost u' :=
  Kernel.ofWeights_real_singleton_lt_iff w
    (fun h ↦ let ⟨u₀, hu₀⟩ := h0; hu₀ (Finset.sum_eq_zero_iff.mp h u₀ (Finset.mem_univ _)))
    (ENNReal.sum_ne_top.mpr fun u _ ↦
      ENNReal.mul_ne_top (weight_rpow_ne_top hα (hle u)) (hctop u))

/-! #### Score speakers

The softmax of an extended-real utility: row `w` is proportional to `exp (score w u)`, so an
utterance of score `⊥`, one literally false at `w` or excluded by a quality gate, is never
produced, and the rationality lives inside the score. Speakers whose utility is not the
informativity utility, such as belief-, question- or politeness-weighted ones, are score
speakers; the power-weight speaker is the score speaker at the informativity utility. -/

section ScoreSpeaker

variable (score : W → U → EReal)

/-- The score speaker has row `w` proportional to the exponential of the score. -/
noncomputable def speakerOfScore : Kernel W U := Kernel.ofWeights fun w u ↦ EReal.exp (score w u)

@[simp] theorem speakerOfScore_apply_singleton (w : W) (u : U) :
    speakerOfScore score w {u} = EReal.exp (score w u) / ∑ u', EReal.exp (score w u') :=
  Kernel.ofWeights_apply_singleton _ w u

instance : IsFiniteKernel (speakerOfScore score) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

variable {score}

omit [MeasurableSingletonClass U] in
/-- The score speaker is a probability kernel whenever every state has an applicable
utterance and no score is `⊤`. -/
theorem isMarkovKernel_speakerOfScore (h0 : ∀ w, ∃ u, score w u ≠ ⊥)
    (htop : ∀ w u, score w u ≠ ⊤) : IsMarkovKernel (speakerOfScore score) :=
  Kernel.isMarkovKernel_ofWeights (fun w ↦ (h0 w).imp fun _ hu ↦ mt EReal.exp_eq_zero_iff.mp hu)
    fun w u ↦ mt EReal.exp_eq_top_iff.mp (htop w u)

/-- An utterance of score `⊥` is never produced. -/
theorem speakerOfScore_apply_singleton_eq_zero {w : W} {u : U} (h : score w u = ⊥) :
    speakerOfScore score w {u} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (by rw [h, EReal.exp_bot])

/-- An applicable utterance is produced with positive mass when no score is `⊤`. -/
theorem speakerOfScore_apply_singleton_ne_zero {w : W} {u : U} (h : score w u ≠ ⊥)
    (htop : ∀ u', score w u' ≠ ⊤) : speakerOfScore score w {u} ≠ 0 :=
  Kernel.ofWeights_apply_singleton_ne_zero (mt EReal.exp_eq_zero_iff.mp h)
    fun u' ↦ mt EReal.exp_eq_top_iff.mp (htop u')

/-- Two states whose scores differ by a real constant across utterances have the same speaker row.
-/
theorem speakerOfScore_apply_eq_of_add {w₁ w₂ : W} {k : ℝ} (h : ∀ u, score w₂ u = score w₁ u + k) :
    speakerOfScore score w₂ = speakerOfScore score w₁ :=
  Kernel.ofWeights_apply_eq_of_mul (mt EReal.exp_eq_zero_iff.mp (EReal.coe_ne_bot k))
    (mt EReal.exp_eq_top_iff.mp (EReal.coe_ne_top k)) fun u ↦ by rw [h, EReal.exp_add]

/-- Two scores differing by a real constant per state give the same speaker, since a term of the
utility that does not depend on the utterance cancels in the softmax. -/
theorem speakerOfScore_eq_of_add {score' : W → U → EReal} {k : W → ℝ}
    (h : ∀ w u, score' w u = score w u + k w) : speakerOfScore score' = speakerOfScore score :=
  Kernel.ofWeights_eq_of_mul (fun w ↦ mt EReal.exp_eq_zero_iff.mp (EReal.coe_ne_bot (k w)))
    (fun w ↦ mt EReal.exp_eq_top_iff.mp (EReal.coe_ne_top (k w))) fun w u ↦ by
      rw [h, EReal.exp_add]

/-- Row preference of the score speaker is score comparison; the normalization cancels. -/
theorem speakerOfScore_real_singleton_lt_iff {w : W} (htop : ∀ u, score w u ≠ ⊤)
    (h0 : ∃ u, score w u ≠ ⊥) {u u' : U} :
    (speakerOfScore score w).real {u} < (speakerOfScore score w).real {u'} ↔
      score w u < score w u' := by
  rw [speakerOfScore, Kernel.ofWeights_real_singleton_lt_iff w
      (fun h ↦ let ⟨u₀, hu₀⟩ := h0
        hu₀ (EReal.exp_eq_zero_iff.mp (Finset.sum_eq_zero_iff.mp h u₀ (Finset.mem_univ _))))
      (ENNReal.sum_ne_top.mpr fun u _ ↦ mt EReal.exp_eq_top_iff.mp (htop u)),
    EReal.exp_lt_exp_iff]

/-- When exactly two utterances are applicable at a state, the share of one is the logistic
function of the score difference. -/
theorem speakerOfScore_real_singleton_of_pair {w : W} {u u' : U} (huu' : u ≠ u')
    (hu : score w u ≠ ⊥) (hu' : score w u' ≠ ⊥) (htop : ∀ v, score w v ≠ ⊤)
    (hsupp : ∀ v, score w v ≠ ⊥ → v = u ∨ v = u') :
    (speakerOfScore score w).real {u} =
      Real.sigmoid ((score w u).toReal - (score w u').toReal) := by
  rw [speakerOfScore, Kernel.ofWeights_real_singleton_of_pair w huu'
      (fun v ↦ mt EReal.exp_eq_top_iff.mp (htop v))
      (fun v hv ↦ hsupp v (mt EReal.exp_eq_zero_iff.mpr hv)),
    ← EReal.coe_toReal (htop u) hu, ← EReal.coe_toReal (htop u') hu', EReal.exp_coe,
    EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.exp_div_add_exp_eq_sigmoid, EReal.toReal_coe,
    EReal.toReal_coe]

omit [MeasurableSingletonClass U] in
/-- The power-weight speaker is the score speaker at the informativity utility, which is the log
of the listener's mass scaled by the rationality plus the log of the cost factor. -/
theorem speaker_eq_speakerOfScore (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W) :
    speaker α cost L =
      speakerOfScore fun w u ↦ ENNReal.log (L u {w}) * α + ENNReal.log (cost u) := by
  unfold speaker speakerOfScore
  congr 1
  funext w u
  rw [EReal.exp_add, EReal.exp_mul, ENNReal.exp_log, ENNReal.exp_log]

end ScoreSpeaker

/-! #### The speaker as a Gibbs measure

A score-speaker row is the Gibbs measure of its score over the applicable utterances, the
uniform measure on them tilted by the score. The Gibbs variational principle then makes the
speaker the rational optimizer: its row maximizes the expected score less the divergence from the
uniform measure on the applicable utterances, with the log partition function as the maximum. -/

section Gibbs

open InformationTheory

variable {score : W → U → EReal} {w : W}

/-- A score-speaker row is the uniform measure on the applicable utterances tilted by the
score. -/
theorem speakerOfScore_eq_tilted (htop : ∀ u, score w u ≠ ⊤) (h0 : ∃ u, score w u ≠ ⊥) :
    speakerOfScore score w =
      (uniformOn {u | score w u ≠ ⊥}).tilted fun u ↦ (score w u).toReal := by
  classical
  set S : Set U := {u | score w u ≠ ⊥}
  have := isProbabilityMeasure_uniformOn S.toFinite h0
  set c : ℝ := ((Measure.count S)⁻¹).toReal
  have hc : c ≠ 0 := ENNReal.toReal_ne_zero.2
    ⟨ENNReal.inv_ne_zero.2 (Measure.count_apply_lt_top.2 S.toFinite).ne,
      ENNReal.inv_ne_top.2 (Measure.count_ne_zero_iff.2 h0)⟩
  have hν (b : U) : (uniformOn S).real {b} = S.indicator (fun _ ↦ c) b := by
    rw [measureReal_def, uniformOn, cond_apply S.toFinite.measurableSet]
    by_cases hb : b ∈ S
    · rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hb), Measure.count_singleton, mul_one,
        Set.indicator_of_mem hb]
    · rw [Set.inter_singleton_eq_empty.2 hb, measure_empty, mul_zero, ENNReal.toReal_zero,
        Set.indicator_of_notMem hb]
  have he (b : U) : (EReal.exp (score w b)).toReal =
      S.indicator (fun b ↦ Real.exp (score w b).toReal) b := by
    by_cases hb : score w b = ⊥
    · rw [hb, EReal.exp_bot, ENNReal.toReal_zero, Set.indicator_of_notMem (by simpa [S] using hb)]
    · rw [Set.indicator_of_mem hb, ← EReal.coe_toReal (htop b) hb, EReal.exp_coe,
        ENNReal.toReal_ofReal (Real.exp_pos _).le, EReal.toReal_coe]
  have key (b : U) : S.indicator (fun _ ↦ c) b * Real.exp (score w b).toReal =
      c * S.indicator (fun b ↦ Real.exp (score w b).toReal) b := by
    by_cases hb : b ∈ S <;> simp [hb]
  refine Measure.ext_iff_singleton.2 fun a ↦ ?_
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, speakerOfScore,
    Kernel.ofWeights_real_singleton (fun w u ↦ EReal.exp (score w u)) w
      (fun u ↦ mt EReal.exp_eq_top_iff.mp (htop u)),
    tilted_real_singleton]
  simp_rw [he, hν, key, ← Finset.mul_sum, mul_div_mul_left _ _ hc]

/-- The score speaker attains the log partition function as its free energy relative to the
uniform measure on the applicable utterances. -/
theorem freeEnergy_speakerOfScore (htop : ∀ u, score w u ≠ ⊤) (h0 : ∃ u, score w u ≠ ⊥) :
    (uniformOn {u | score w u ≠ ⊥}).freeEnergy (fun u ↦ (score w u).toReal)
        (speakerOfScore score w) =
      cgf (fun u ↦ (score w u).toReal) (uniformOn {u | score w u ≠ ⊥}) 1 := by
  have := isProbabilityMeasure_uniformOn (Set.toFinite {u | score w u ≠ ⊥}) h0
  rw [speakerOfScore_eq_tilted htop h0]
  exact freeEnergy_tilted _ .of_finite .of_finite .of_finite

/-- The score speaker is the rational optimizer. Among the distributions absolutely continuous
with respect to the uniform measure on the applicable utterances, its row has the greatest
expected score less divergence from that uniform measure. -/
theorem isGreatest_freeEnergy_speakerOfScore (htop : ∀ u, score w u ≠ ⊤)
    (h0 : ∃ u, score w u ≠ ⊥) :
    IsGreatest ((uniformOn {u | score w u ≠ ⊥}).freeEnergy (fun u ↦ (score w u).toReal) ''
        {q | IsProbabilityMeasure q ∧ q ≪ uniformOn {u | score w u ≠ ⊥} ∧
          Integrable (llr q (uniformOn {u | score w u ≠ ⊥})) q ∧
          Integrable (fun u ↦ (score w u).toReal) q})
      ((uniformOn {u | score w u ≠ ⊥}).freeEnergy (fun u ↦ (score w u).toReal)
        (speakerOfScore score w)) := by
  have := isProbabilityMeasure_uniformOn (Set.toFinite {u | score w u ≠ ⊥}) h0
  rw [freeEnergy_speakerOfScore htop h0]
  exact isGreatest_cgf _ .of_finite .of_finite .of_finite

end Gibbs

open Filter Topology in
/-- As rationality grows, the speaker puts all its mass on the utterance the listener most favors
at `w`, so the fully rational speaker is the argmax speaker. -/
theorem tendsto_speaker_real_singleton_atTop {cost : U → ℝ≥0∞} (hc0 : ∀ u, cost u ≠ 0)
    (hctop : ∀ u, cost u ≠ ∞) {L : Kernel U W} {w : W} (hle : ∀ u, L u {w} ≤ 1) {u : U}
    (hu : L u {w} ≠ 0) (hmax : ∀ u' ≠ u, L u' {w} < L u {w}) :
    Tendsto (fun α ↦ (speaker α cost L w).real {u}) atTop (𝓝 1) := by
  classical
  set ℓ : U → ℝ := fun v ↦ (L v {w}).toReal
  set κ : U → ℝ := fun v ↦ (cost v).toReal
  have hℓ0 (v : U) : 0 ≤ ℓ v := ENNReal.toReal_nonneg
  have hℓu : 0 < ℓ u := ENNReal.toReal_pos hu (ne_top_of_le_ne_top ENNReal.one_ne_top (hle u))
  have hκ (v : U) : 0 < κ v := ENNReal.toReal_pos (hc0 v) (hctop v)
  have hform : ∀ᶠ α in atTop,
      (∑ v, (ℓ v / ℓ u) ^ α * (κ v / κ u))⁻¹ = (speaker α cost L w).real {u} := by
    filter_upwards [eventually_ge_atTop 0] with α hα
    have hsum : ∑ v, (ℓ v / ℓ u) ^ α * (κ v / κ u) = (∑ v, ℓ v ^ α * κ v) / (ℓ u ^ α * κ u) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [Real.div_rpow (hℓ0 v) hℓu.le, div_mul_div_comm]
    rw [speaker_real_singleton hα hctop hle, hsum, inv_div]
    simp only [ℓ, κ, ENNReal.toReal_rpow]
  have hlim : Tendsto (fun α : ℝ ↦ ∑ v, (ℓ v / ℓ u) ^ α * (κ v / κ u)) atTop
      (𝓝 (∑ v, if v = u then (1 : ℝ) else 0)) := by
    refine tendsto_finsetSum _ fun v _ ↦ ?_
    by_cases hv : v = u
    · subst hv
      simp [div_self hℓu.ne', div_self (hκ v).ne']
    · have hlt : ℓ v / ℓ u < 1 := (div_lt_one hℓu).2
        (ENNReal.toReal_strict_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (hle u)) (hmax v hv))
      have h1 := (tendsto_rpow_atTop_of_base_lt_one _
        (by linarith [div_nonneg (hℓ0 v) hℓu.le]) hlt).mul_const (κ v / κ u)
      rw [zero_mul] at h1
      simpa only [hv, ite_false] using h1
  rw [Finset.sum_ite_eq' Finset.univ u, ite_eq_left (Finset.mem_univ u)] at hlim
  simpa using (hlim.inv₀ one_ne_zero).congr' hform

/-- With Boolean meanings and a constant cost, a state two utterances both fit produces the
utterance with the smaller extension more often, since informativity is the inverse of extension
mass. -/
theorem speaker_literalListener_indicator_real_singleton_lt_iff [DiscreteMeasurableSpace W]
    {α : ℝ} (hα : 0 < α) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞) (μ : Measure W)
    [IsFiniteMeasure μ] (sem : U → Set W) {w : W} (hμ : μ {w} ≠ 0) {u u' : U} (hu : w ∈ sem u)
    (hu' : w ∈ sem u') :
    (speaker α (fun _ ↦ c) (literalListener μ fun u ↦ (sem u).indicator 1) w).real {u}
        < (speaker α (fun _ ↦ c) (literalListener μ fun u ↦ (sem u).indicator 1) w).real {u'}
      ↔ μ (sem u') < μ (sem u) := by
  have hle : ∀ v, literalListener μ (fun u ↦ (sem u).indicator 1) v {w} ≤ 1 := fun v ↦ by
    by_cases h : w ∈ sem v
    · exact literalListener_indicator_apply_singleton_le_one μ sem (measure_ne_top _ _) h
    · rw [literalListener_indicator_apply_singleton_of_notMem μ sem h]; exact zero_le_one
  have hne : literalListener μ (fun u ↦ (sem u).indicator 1) u {w} ≠ 0 := by
    rw [literalListener_indicator_apply_singleton μ sem hu]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hμ
  have key : ∀ {a b c : ℝ≥0∞}, c ≠ 0 → c ≠ ∞ → (a * c < b * c ↔ a < b) := fun h0 htop ↦
    ⟨fun h ↦ lt_of_not_ge fun hab ↦ absurd h (not_lt.mpr (mul_le_mul' hab le_rfl)),
      ENNReal.mul_lt_mul_left h0 htop⟩
  rw [speaker_real_singleton_lt_iff hα.le (fun _ ↦ hctop) hle
      ⟨u, mul_ne_zero (weight_rpow_ne_zero hα.le hne) hc0⟩,
    key hc0 hctop, ENNReal.rpow_lt_rpow_iff hα, literalListener_indicator_apply_singleton μ sem hu,
    literalListener_indicator_apply_singleton μ sem hu', key hμ (measure_ne_top _ _),
    ENNReal.inv_lt_inv]

/-! #### Pragmatic listeners -/

section Listener

variable [StandardBorelSpace W] [Nonempty W] (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W)
  (μ : Measure W) [IsFiniteMeasure μ]

/-- The pragmatic listener (eq. 3) is the Bayesian inverse of the speaker against the prior. -/
noncomputable def pragmaticListener : Kernel U W := (speaker α cost L)†μ

instance : IsMarkovKernel (pragmaticListener α cost L μ) :=
  inferInstanceAs (IsMarkovKernel ((speaker α cost L)†μ))

omit [StandardBorelSpace W] [Nonempty W] in
/-- With Boolean meanings, hearing an utterance rules out every state it does not fit, once some
state it fits has prior mass. -/
theorem pragmaticListener_literalListener_indicator_apply_singleton_of_notMem
    [DiscreteMeasurableSpace W] [StandardBorelSpace W] [Nonempty W] (hα : 0 < α)
    (hc0 : ∀ u, cost u ≠ 0) (hctop : ∀ u, cost u ≠ ∞) (sem : U → Set W) {u : U} {w w' : W}
    (hw : w ∉ sem u) (hw' : w' ∈ sem u) (hμ : μ {w'} ≠ 0) :
    pragmaticListener α cost (literalListener μ fun u ↦ (sem u).indicator 1) μ u {w} = 0 := by
  have hle : ∀ v, literalListener μ (fun u ↦ (sem u).indicator 1) v {w'} ≤ 1 := fun v ↦ by
    by_cases h : w' ∈ sem v
    · exact literalListener_indicator_apply_singleton_le_one μ sem (measure_ne_top _ _) h
    · rw [literalListener_indicator_apply_singleton_of_notMem μ sem h]; exact zero_le_one
  have hS : speaker α cost (literalListener μ fun u ↦ (sem u).indicator 1) w' {u} ≠ 0 :=
    speaker_apply_singleton_ne_zero hα.le hc0 hctop hle (by
      rw [literalListener_indicator_apply_singleton μ sem hw']
      exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hμ)
  rw [pragmaticListener, posterior_apply_singleton _ _ (comp_apply_singleton_ne_zero _ _ hμ hS),
    speaker_apply_singleton_eq_zero hα
      (literalListener_indicator_apply_singleton_of_notMem μ sem hw)]
  simp

/-- At a prior giving every state the same positive mass, listener preference between two
states is speaker preference between them, since the prior and the marginal cancel. -/
theorem pragmaticListener_real_lt_iff (hμeq : ∀ w w', μ {w} = μ {w'}) (hμ0 : ∀ w, μ {w} ≠ 0)
    {u : U} {w₀ : W} (hs : speaker α cost L w₀ {u} ≠ 0) {w₁ w₂ : W} :
    (pragmaticListener α cost L μ u).real {w₁} < (pragmaticListener α cost L μ u).real {w₂}
      ↔ (speaker α cost L w₁).real {u} < (speaker α cost L w₂).real {u} :=
  posterior_real_singleton_lt_iff_of_eq _ _ (comp_apply_singleton_ne_zero _ _ (hμ0 w₀) hs)
    (hμeq w₁ w₂) (hμ0 w₁)

variable [DiscreteMeasurableSpace U] [StandardBorelSpace U] [Nonempty U] [DecidableEq O]
  (obs : U → O)

omit [Countable W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U]
  [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace U] [Nonempty U] [DecidableEq O] in
theorem measurable_obs_snd : Measurable fun p : W × U ↦ obs p.2 :=
  Measurable.of_discrete.comp measurable_snd

/-- The joint pragmatic listener (eqs. 18b/21b) applies when the listener hears only the form `obs
u` of the speaker's choice. The posterior over (state, choice) is then the Bayesian inverse of the
deterministic observation kernel against the joint of prior and speaker. Its `fst` is the state
listener, its `snd` the choice posterior. -/
noncomputable def jointListener : Kernel O (W × U) :=
  (Kernel.deterministic (fun p : W × U ↦ obs p.2) (measurable_obs_snd obs))†(μ ⊗ₘ speaker α cost L)

omit [MeasurableSingletonClass U] [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace U]
  [Nonempty U] [DecidableEq O] [IsFiniteMeasure μ] in
/-- The heard form is distributed as the production marginal. -/
theorem deterministic_comp_compProd_speaker :
    Kernel.deterministic (fun p : W × U ↦ obs p.2) (measurable_obs_snd obs)
        ∘ₘ (μ ⊗ₘ speaker α cost L)
      = (speaker α cost L ∘ₘ μ).map obs := by
  rw [Measure.deterministic_comp_eq_map, show (fun p : W × U ↦ obs p.2) = obs ∘ Prod.snd from rfl,
    ← Measure.map_map Measurable.of_discrete measurable_snd, ← Measure.snd, Measure.snd_compProd]

omit [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace U] [Nonempty U] [DecidableEq O]
  [IsFiniteMeasure μ] in
/-- A positive-prior state with a positively produced `o`-shaped utterance witnesses a
positive observation marginal. -/
theorem map_comp_speaker_ne_zero [MeasurableSingletonClass O] {w : W} {u : U} {o : O}
    (hμ : μ {w} ≠ 0) (hu : obs u = o) (hs : speaker α cost L w {u} ≠ 0) :
    ((speaker α cost L ∘ₘ μ).map obs) {o} ≠ 0 := by
  rw [Measure.map_apply Measurable.of_discrete (.singleton o)]
  intro h
  exact comp_apply_singleton_ne_zero _ _ hμ hs
    (measure_mono_null (Set.singleton_subset_iff.mpr (by simp [hu])) h)

variable [MeasurableSingletonClass O]

/-- Exact Bayes for the joint listener at a positive-mass observation. -/
theorem jointListener_apply_singleton {o : O} (ho : ((speaker α cost L ∘ₘ μ).map obs) {o} ≠ 0)
    (w : W) (u : U) :
    jointListener α cost L μ obs o {(w, u)}
      = (if obs u = o then μ {w} * speaker α cost L w {u} else 0)
        / ((speaker α cost L ∘ₘ μ).map obs) {o} := by
  rw [jointListener, posterior_apply_singleton _ _
      (by rwa [deterministic_comp_compProd_speaker]),
    deterministic_comp_compProd_speaker, ← Set.singleton_prod_singleton,
    Measure.compProd_apply_prod (.singleton w) (.singleton u), lintegral_singleton,
    Kernel.deterministic_apply' _ _ (.singleton o)]
  simp only [Set.indicator_apply, Set.mem_singleton_iff]
  split_ifs <;> simp [mul_comm]

/-- The joint listener prefers the state with the greater prior-weighted speaker mass pooled
over the observation's fibre, since the observation's marginal cancels. -/
theorem jointListener_fst_real_lt_iff [Fintype W] {o : O}
    (ho : ((speaker α cost L ∘ₘ μ).map obs) {o} ≠ 0) (w₁ w₂ : W) :
    (jointListener α cost L μ obs o).fst.real {w₁}
        < (jointListener α cost L μ obs o).fst.real {w₂}
      ↔ (∑ u ∈ Finset.univ.filter (obs · = o), μ.real {w₁} * (speaker α cost L w₁).real {u})
        < ∑ u ∈ Finset.univ.filter (obs · = o), μ.real {w₂} * (speaker α cost L w₂).real {u} := by
  have key : ∀ w : W, (jointListener α cost L μ obs o).fst {w}
      = (∑ u ∈ Finset.univ.filter (obs · = o), μ {w} * speaker α cost L w {u})
        / ((speaker α cost L ∘ₘ μ).map obs) {o} := fun w ↦ by
    rw [Measure.fst_apply_singleton]
    simp_rw [jointListener_apply_singleton α cost L μ obs ho, div_eq_mul_inv, ← Finset.sum_mul,
      ← Finset.sum_filter]
  have hne : ∀ w : W,
      (∑ u ∈ Finset.univ.filter (obs · = o), μ {w} * speaker α cost L w {u}) ≠ ∞ :=
    fun w ↦ ENNReal.sum_ne_top.mpr fun u _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, key, key,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne w₁) ho) (ENNReal.div_ne_top (hne w₂) ho),
    ENNReal.div_lt_div_iff_left ho (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne w₁) (hne w₂),
    ENNReal.toReal_sum (fun u _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun u _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

/-- Choice-posterior preference among `o`-shaped choices reduces to comparing prior-weighted
speaker masses across states. -/
theorem jointListener_snd_real_lt_iff [Fintype W] {o : O}
    (ho : ((speaker α cost L ∘ₘ μ).map obs) {o} ≠ 0) {u₁ u₂ : U}
    (h₁ : obs u₁ = o) (h₂ : obs u₂ = o) :
    (jointListener α cost L μ obs o).snd.real {u₁}
        < (jointListener α cost L μ obs o).snd.real {u₂}
      ↔ (∑ w, μ.real {w} * (speaker α cost L w).real {u₁})
        < ∑ w, μ.real {w} * (speaker α cost L w).real {u₂} := by
  have key : ∀ u, obs u = o → (jointListener α cost L μ obs o).snd {u}
      = (∑ w, μ {w} * speaker α cost L w {u}) / ((speaker α cost L ∘ₘ μ).map obs) {o} :=
    fun u hu ↦ by
      rw [Measure.snd_apply_singleton]
      simp_rw [jointListener_apply_singleton α cost L μ obs ho, ite_eq_left hu, div_eq_mul_inv,
        ← Finset.sum_mul]
  have hne : ∀ u : U, (∑ w, μ {w} * speaker α cost L w {u}) ≠ ∞ := fun u ↦
    ENNReal.sum_ne_top.mpr fun w _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, key u₁ h₁, key u₂ h₂,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne u₁) ho) (ENNReal.div_ne_top (hne u₂) ho),
    ENNReal.div_lt_div_iff_left ho (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne u₁) (hne u₂),
    ENNReal.toReal_sum (fun w _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun w _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

end Listener

/-! #### State-side latent families

In Franke and Bergen's lexical-uncertainty model (eqs. 11–13) each speaker carries a fixed latent
index and best-responds within it. Normalization is per index, in contrast to the
choice-side latents of `jointListener`, whose speaker normalizes across the pooled pairs.
The weight functions coincide; only the normalization differs. -/

section Family

variable {Λ : Type*} [MeasurableSpace Λ] [Countable Λ] [MeasurableSingletonClass Λ]

/-- The family speaker carries the latent index in the state. -/
noncomputable def familySpeaker (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞) :
    Kernel (W × Λ) U :=
  Kernel.ofFunOfCountable fun p ↦ speaker α cost (L p.2) p.1

omit [MeasurableSingletonClass U] in
@[simp] theorem familySpeaker_apply (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞)
    (p : W × Λ) : familySpeaker L α cost p = speaker α cost (L p.2) p.1 := rfl

instance (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞) :
    IsFiniteKernel (familySpeaker L α cost) :=
  ⟨⟨1, ENNReal.one_lt_top, fun p ↦ by
    rw [familySpeaker_apply]
    exact Kernel.ofWeights_apply_univ_le_one _ p.1⟩⟩

/-- A member's positively produced utterance at a positive-prior state witnesses a positive
observation marginal for the family speaker. -/
theorem comp_familySpeaker_ne_zero {L : Λ → Kernel U W} {α : ℝ} {cost : U → ℝ≥0∞}
    {μ : Measure (W × Λ)} {w : W} {l : Λ} {u : U} (hμ : μ {(w, l)} ≠ 0)
    (hs : speaker α cost (L l) w {u} ≠ 0) : (familySpeaker L α cost ∘ₘ μ) {u} ≠ 0 :=
  comp_apply_singleton_ne_zero _ _ hμ (by rwa [familySpeaker_apply])

variable [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace Λ] [Nonempty Λ]

/-- The family listener (eqs. 12–13) is the Bayesian inverse of the family speaker over the joint
(state, index) space. -/
noncomputable def familyListener (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞)
    (μ : Measure (W × Λ)) [IsFiniteMeasure μ] : Kernel U (W × Λ) :=
  (familySpeaker L α cost)†μ

variable {μ : Measure (W × Λ)} [IsFiniteMeasure μ]

/-- Exact Bayes for the family listener at a positive-mass utterance. -/
theorem familyListener_apply_singleton (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞) {u : U}
    (hu : (familySpeaker L α cost ∘ₘ μ) {u} ≠ 0) (p : W × Λ) :
    familyListener L α cost μ u {p}
      = μ {p} * speaker α cost (L p.2) p.1 {u} / (familySpeaker L α cost ∘ₘ μ) {u} := by
  rw [familyListener, posterior_apply_singleton _ _ hu, familySpeaker_apply]

/-- A pair at which the utterance is never produced receives no posterior mass. -/
theorem familyListener_apply_singleton_eq_zero (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞)
    {u : U} (hu : (familySpeaker L α cost ∘ₘ μ) {u} ≠ 0) {p : W × Λ}
    (hp : speaker α cost (L p.2) p.1 {u} = 0) : familyListener L α cost μ u {p} = 0 := by
  rw [familyListener_apply_singleton L α cost hu, hp, mul_zero, ENNReal.zero_div]

/-- A relabelling of states, latents and utterances that carries one family of literal listeners
and prior to another carries the family listener along, with the cost relabelled. -/
theorem familyListener_apply_singleton_of_equiv [Fintype W] [Fintype Λ] (e : W ≃ W) (f : Λ ≃ Λ)
    (τ : U ≃ U) (L L' : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞) {μ' : Measure (W × Λ)}
    [IsFiniteMeasure μ'] (hL : ∀ l v w, L' (f l) (τ v) {e w} = L l v {w})
    (hμ : ∀ w l, μ' {(e w, f l)} = μ {(w, l)}) {u : U}
    (hu : (familySpeaker L α (cost ∘ τ) ∘ₘ μ) {u} ≠ 0) (w : W) (l : Λ) :
    familyListener L' α cost μ' (τ u) {(e w, f l)} = familyListener L α (cost ∘ τ) μ u {(w, l)} :=
  posterior_apply_singleton_of_equiv _ _ (e.prodCongr f) (fun p ↦ hμ p.1 p.2)
    (fun p ↦ by
      rw [Equiv.prodCongr_apply, Prod.map, familySpeaker_apply, familySpeaker_apply]
      exact speaker_apply_singleton_of_equiv τ α cost (fun v ↦ hL p.2 v p.1) u) hu (w, l)

/-- The state marginal of the family listener is positive at a state exactly when some latent
pairs a positive prior with a positively produced utterance. -/
theorem familyListener_fst_apply_singleton_ne_zero_iff [Fintype Λ] (L : Λ → Kernel U W) (α : ℝ)
    (cost : U → ℝ≥0∞) {u : U} (hu : (familySpeaker L α cost ∘ₘ μ) {u} ≠ 0) (w : W) :
    (familyListener L α cost μ u).fst {w} ≠ 0
      ↔ ∃ l, μ {(w, l)} ≠ 0 ∧ speaker α cost (L l) w {u} ≠ 0 := by
  rw [Measure.fst_apply_singleton, ne_eq, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, familyListener_apply_singleton L α cost hu,
    ENNReal.div_eq_zero_iff, mul_eq_zero, not_forall, not_or]
  exact ⟨fun ⟨l, h⟩ ↦ ⟨l, h.1⟩, fun ⟨l, h⟩ ↦ ⟨l, h, measure_ne_top _ _⟩⟩

/-- On reals the state marginal of the family listener over a product prior is the prior at the
state times the latent-averaged member speaker share, over the observation marginal. -/
theorem familyListener_fst_real_singleton [Fintype Λ] (L : Λ → Kernel U W) (α : ℝ)
    (cost : U → ℝ≥0∞) (μW : Measure W) [IsFiniteMeasure μW] (ν : Measure Λ) [IsFiniteMeasure ν]
    {u : U} (hu : (familySpeaker L α cost ∘ₘ μW.prod ν) {u} ≠ 0) (w : W) :
    (familyListener L α cost (μW.prod ν) u).fst.real {w}
      = μW.real {w} * (∑ l, ν.real {l} * (speaker α cost (L l) w).real {u})
        / (familySpeaker L α cost ∘ₘ μW.prod ν).real {u} := by
  rw [familyListener, posterior_fst_real_singleton _ _ hu, Finset.mul_sum]
  simp_rw [Measure.prod_real_singleton, familySpeaker_apply, mul_assoc]

/-- Event comparison for the family listener reduces to prior-weighted member speaker
sums. -/
theorem familyListener_real_lt_iff (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞) {u : U}
    (hu : (familySpeaker L α cost ∘ₘ μ) {u} ≠ 0) (E₁ E₂ : Finset (W × Λ)) :
    (familyListener L α cost μ u).real ↑E₁ < (familyListener L α cost μ u).real ↑E₂
      ↔ (∑ p ∈ E₁, μ.real {p} * (speaker α cost (L p.2) p.1).real {u})
        < ∑ p ∈ E₂, μ.real {p} * (speaker α cost (L p.2) p.1).real {u} := by
  rw [familyListener, posterior_real_finset_lt_iff _ _ hu]
  simp_rw [familySpeaker_apply]

/-- At equal priors, the family listener's state marginal prefers the state with the greater
speaker share summed over the latent family. -/
theorem familyListener_fst_real_lt_iff [Fintype Λ] (L : Λ → Kernel U W) {α : ℝ}
    {cost : U → ℝ≥0∞} (hμeq : ∀ p q : W × Λ, μ {p} = μ {q}) (hμ0 : ∀ p : W × Λ, μ {p} ≠ 0)
    {u : U} {w₀ : W} {l₀ : Λ} (hs : speaker α cost (L l₀) w₀ {u} ≠ 0) {w₁ w₂ : W} :
    (familyListener L α cost μ u).fst.real {w₁} < (familyListener L α cost μ u).fst.real {w₂}
      ↔ (∑ l, (speaker α cost (L l) w₁).real {u}) < ∑ l, (speaker α cost (L l) w₂).real {u} := by
  set p₀ : W × Λ := Classical.arbitrary _
  have key : ∀ w : W, (∑ l, μ.real {(w, l)} * (familySpeaker L α cost (w, l)).real {u})
      = μ.real {p₀} * ∑ l, (speaker α cost (L l) w).real {u} := fun w ↦ by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by
      rw [familySpeaker_apply, show μ.real {(w, l)} = μ.real {p₀} from by
        rw [measureReal_def, measureReal_def, hμeq (w, l) p₀]]
  rw [familyListener,
    posterior_fst_real_lt_iff _ _ (comp_familySpeaker_ne_zero (hμ0 (w₀, l₀)) hs), key, key,
    mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real {p₀} from ENNReal.toReal_pos (hμ0 p₀) (measure_ne_top _ _))]

/-- At equal priors, the family listener's latent marginal prefers the member with the greater
speaker share summed over the states. -/
theorem familyListener_snd_real_lt_iff [Fintype W] (L : Λ → Kernel U W) {α : ℝ}
    {cost : U → ℝ≥0∞} (hμeq : ∀ p q : W × Λ, μ {p} = μ {q}) (hμ0 : ∀ p : W × Λ, μ {p} ≠ 0)
    {u : U} {w₀ : W} {l₀ : Λ} (hs : speaker α cost (L l₀) w₀ {u} ≠ 0) {l₁ l₂ : Λ} :
    (familyListener L α cost μ u).snd.real {l₁} < (familyListener L α cost μ u).snd.real {l₂}
      ↔ (∑ w, (speaker α cost (L l₁) w).real {u}) < ∑ w, (speaker α cost (L l₂) w).real {u} := by
  set p₀ : W × Λ := Classical.arbitrary _
  have key : ∀ l : Λ, (∑ w, μ.real {(w, l)} * (familySpeaker L α cost (w, l)).real {u})
      = μ.real {p₀} * ∑ w, (speaker α cost (L l) w).real {u} := fun l ↦ by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ ↦ by
      rw [familySpeaker_apply, show μ.real {(w, l)} = μ.real {p₀} from by
        rw [measureReal_def, measureReal_def, hμeq (w, l) p₀]]
  rw [familyListener,
    posterior_snd_real_lt_iff _ _ (comp_familySpeaker_ne_zero (hμ0 (w₀, l₀)) hs), key, key,
    mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real {p₀} from ENNReal.toReal_pos (hμ0 p₀) (measure_ne_top _ _))]

/-- A pair producing the utterance with certainty outweighs any event of smaller total prior
mass, in that the listener's posterior on the pair's event exceeds that event's. -/
theorem familyListener_real_lt_of_certain (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞)
    {u : U} {E₁ E₂ : Finset (W × Λ)} {p₀ : W × Λ} (hp₀ : p₀ ∈ E₂)
    (hs : speaker α cost (L p₀.2) p₀.1 {u} = 1) (hlt : (∑ p ∈ E₁, μ.real {p}) < μ.real {p₀}) :
    (familyListener L α cost μ u).real ↑E₁ < (familyListener L α cost μ u).real ↑E₂ := by
  have hpos : 0 < μ.real {p₀} :=
    (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg).trans_lt hlt
  rw [familyListener_real_lt_iff L α cost
    (comp_familySpeaker_ne_zero (w := p₀.1) (l := p₀.2) (ENNReal.toReal_pos_iff.mp hpos).1.ne'
      (hs ▸ one_ne_zero))]
  calc ∑ p ∈ E₁, μ.real {p} * (speaker α cost (L p.2) p.1).real {u}
      ≤ ∑ p ∈ E₁, μ.real {p} := Finset.sum_le_sum fun p _ ↦
        mul_le_of_le_one_right measureReal_nonneg (speaker_real_singleton_le_one _ _ _ _ _)
    _ < μ.real {p₀} := hlt
    _ = μ.real {p₀} * (speaker α cost (L p₀.2) p₀.1).real {u} := by
        rw [measureReal_def (μ := speaker α cost (L p₀.2) p₀.1), hs, ENNReal.toReal_one, mul_one]
    _ ≤ ∑ p ∈ E₂, μ.real {p} * (speaker α cost (L p.2) p.1).real {u} :=
        Finset.single_le_sum (f := fun p ↦ μ.real {p} * (speaker α cost (L p.2) p.1).real {u})
          (fun p _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg) hp₀

end Family

end Pipeline

end RSA
