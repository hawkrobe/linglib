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
comparison of latent-variable variants (eqs. 5–22). The literal listener conditions the prior on
the extension of the utterance, or, at a graded meaning, reweights the prior by it; the speaker is
the softmax of Frank and Goodman's utility, the log of the listener's mass less a real cost,
scaled by the rationality; and the pragmatic listeners are mathlib's posterior kernels `κ†μ`,
of the speaker, or of the deterministic observation kernel over the joint of prior and speaker
when the listener hears only the form of the speaker's choice. Rationality, cost, meaning, and
prior are arguments, so findings quantify over them. The uniform-prior Boolean specialization
with its decision procedure is `Linglib.Pragmatics.RSA.Uniform`.

## Main definitions

* `RSA.literalListener` — eq. 1: the prior conditioned on the extension of the utterance.
* `RSA.gradedListener` — the prior reweighted by a graded meaning; on an indicator meaning it is
  the literal listener (`RSA.gradedListener_indicator`).
* `RSA.speakerOfScore` — the softmax of an extended-real utility, `⊥` marking the
  inapplicable utterances.
* `RSA.speaker` — eqs. 2/6–7: the score speaker at the utility `α * (log L - C)`; its weights
  are `L ^ α * exp (-(α * C))` (`RSA.speaker_eq_ofWeights`).
* `RSA.pragmaticListener` — eq. 3: the Bayesian inverse `S†μ` of a speaker `S` against the
  prior.
* `RSA.jointListener` — eqs. 18b/21b: the posterior over (state, choice) given the heard
  form; `.fst` is the state listener, `.snd` the choice posterior.
* `RSA.familySpeaker` — state-side latents (eqs. 11–13): the latent is a speaker argument and
  normalization is per latent; its listener is `pragmaticListener (familySpeaker L α C) μ`.

## Main results

* `RSA.speaker_literalListener_real_singleton_lt_iff` — with Boolean meanings a
  state prefers the utterance with the smaller extension.
* `RSA.speaker_literalListener_congr`,
  `RSA.speaker_literalListener_le_of_subset` — with Boolean meanings the speaker sees a
  state only through the utterances true at it, and produces each of them less the more there are.
* `RSA.jointListener_apply_singleton` — exact Bayes for the joint listener.
* `RSA.speakerOfScore_eq_tilted`, `RSA.isGreatest_freeEnergy_speakerOfScore` — a score-speaker
  row is the Gibbs measure of its score over the applicable utterances, and so the rational
  optimizer: it maximizes the expected score less the divergence from the uniform measure on
  them (the Gibbs variational principle).
* `RSA.tendsto_speaker_real_singleton_atTop` — as rationality grows the speaker puts all its mass
  on the utterance the listener most favors.
* `RSA.jointListener_fst_real_lt_iff`, `RSA.jointListener_snd_real_lt_iff`,
  `RSA.pragmaticListener_fst_real_lt_iff`, `RSA.pragmaticListener_snd_real_lt_iff` — listener
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

/-- The literal listener (eq. 1) conditions the prior on the extension of the utterance. -/
noncomputable def literalListener (μ : Measure W) (sem : U → Set W) : Kernel U W :=
  Kernel.ofFunOfCountable fun u ↦ μ[|sem u]

theorem literalListener_apply (μ : Measure W) (sem : U → Set W) (u : U) :
    literalListener μ sem u = μ[|sem u] := rfl

/-- Each row of the literal listener is a probability measure or zero, so it is a finite
kernel. -/
instance (μ : Measure W) (sem : U → Set W) : IsFiniteKernel (literalListener μ sem) :=
  ⟨⟨1, ENNReal.one_lt_top, fun u ↦ by rw [literalListener_apply]; exact prob_le_one⟩⟩

/-- The graded literal listener reweights the prior by a graded meaning of the utterance and
renormalizes. -/
noncomputable def gradedListener (μ : Measure W) (m : U → W → ℝ≥0∞) : Kernel U W :=
  Kernel.ofFunOfCountable fun u ↦ (μ.withDensity (m u))[|Set.univ]

theorem gradedListener_apply (μ : Measure W) (m : U → W → ℝ≥0∞) (u : U) :
    gradedListener μ m u = (μ.withDensity (m u))[|Set.univ] := rfl

instance (μ : Measure W) (m : U → W → ℝ≥0∞) : IsFiniteKernel (gradedListener μ m) :=
  ⟨⟨1, ENNReal.one_lt_top, fun u ↦ by rw [gradedListener_apply]; exact prob_le_one⟩⟩

/-- On a Boolean meaning the graded literal listener is the literal listener. -/
theorem gradedListener_indicator [DiscreteMeasurableSpace W] (μ : Measure W) (sem : U → Set W) :
    gradedListener μ (fun u ↦ (sem u).indicator 1) = literalListener μ sem :=
  Kernel.ext fun u ↦ by
    rw [gradedListener_apply, literalListener_apply, withDensity_indicator_one .of_discrete]
    simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.restrict_apply_univ]

/-- The graded literal listener at an utterance depends on that utterance's meaning only up to a
positive finite scalar, which the normalization absorbs. -/
theorem gradedListener_apply_eq_of_eq_mul (μ : Measure W) {m m' : U → W → ℝ≥0∞} {u : U}
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (h : ∀ w, m' u w = c * m u w) :
    gradedListener μ m' u = gradedListener μ m u := by
  rw [gradedListener_apply, gradedListener_apply,
    show μ.withDensity (m' u) = c • μ.withDensity (m u) by
      rw [show m' u = fun w ↦ c * m u w from funext h]; exact withDensity_smul' c (m u) hc]
  ext s hs
  rw [cond_apply MeasurableSet.univ, cond_apply MeasurableSet.univ, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hc),
    mul_mul_mul_comm, ENNReal.inv_mul_cancel hc0 hc, one_mul]

/-- The graded literal listener depends on the meaning only up to a positive finite scalar. -/
theorem gradedListener_const_mul (μ : Measure W) (m : U → W → ℝ≥0∞) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ∞) : gradedListener μ (fun u w ↦ c * m u w) = gradedListener μ m :=
  Kernel.ext fun _ ↦ gradedListener_apply_eq_of_eq_mul μ hc0 hc fun _ ↦ rfl

/-- Every finite measure on a countable discrete space is a graded literal listener at a prior of
positive mass everywhere, with the measure's density against the prior as the meaning. -/
theorem gradedListener_div [Countable W] [MeasurableSingletonClass W] (μ : Measure W)
    [IsFiniteMeasure μ] (hμ : ∀ w, μ {w} ≠ 0) (ν : U → Measure W) (u : U) :
    gradedListener μ (fun u w ↦ ν u {w} / μ {w}) u = (ν u)[|Set.univ] := by
  rw [gradedListener_apply]
  congr 1
  refine Measure.ext_of_singleton fun w ↦ ?_
  rw [withDensity_apply _ (.singleton w), lintegral_singleton,
    ENNReal.div_mul_cancel (hμ w) (measure_ne_top μ _)]

theorem gradedListener_apply_singleton' [MeasurableSingletonClass W] (μ : Measure W)
    (m : U → W → ℝ≥0∞) (u : U) (w : W) :
    gradedListener μ m u {w} = m u w * μ {w} / ∫⁻ w', m u w' ∂μ := by
  rw [gradedListener_apply, cond_apply MeasurableSet.univ, Set.univ_inter,
    withDensity_apply _ (.singleton w), lintegral_singleton, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ENNReal.div_eq_inv_mul]

theorem gradedListener_apply_singleton [Fintype W] [MeasurableSingletonClass W] (μ : Measure W)
    (m : U → W → ℝ≥0∞) (u : U) (w : W) :
    gradedListener μ m u {w} = m u w * μ {w} / ∑ w', m u w' * μ {w'} := by
  rw [gradedListener_apply_singleton', lintegral_fintype]

/-- A relabelling of the states that carries one prior and meaning to another carries the graded
literal listener along. -/
theorem gradedListener_apply_singleton_of_equiv {W' U' : Type*} [MeasurableSpace W']
    [MeasurableSpace U'] [Countable U'] [MeasurableSingletonClass U'] [Fintype W]
    [MeasurableSingletonClass W] [Fintype W'] [MeasurableSingletonClass W'] (e : W ≃ W')
    {μ : Measure W} {μ' : Measure W'} {m : U → W → ℝ≥0∞} {m' : U' → W' → ℝ≥0∞} {u : U} {u' : U'}
    (hμ : ∀ w, μ' {e w} = μ {w}) (hm : ∀ w, m' u' (e w) = m u w) (w : W) :
    gradedListener μ' m' u' {e w} = gradedListener μ m u {w} := by
  rw [gradedListener_apply_singleton, gradedListener_apply_singleton, hm, hμ, ← e.sum_comp]
  simp only [hm, hμ]

/-- The graded literal listener of an utterance whose meaning has positive finite mass under the
prior is a probability measure. -/
theorem isProbabilityMeasure_gradedListener (μ : Measure W) (m : U → W → ℝ≥0∞) (u : U)
    (h0 : ∫⁻ w, m u w ∂μ ≠ 0) (htop : ∫⁻ w, m u w ∂μ ≠ ∞) :
    IsProbabilityMeasure (gradedListener μ m u) := by
  rw [gradedListener_apply]
  refine cond_isProbabilityMeasure_of_finite ?_ ?_ <;>
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- Marginalizing a joint graded listener whose meaning depends on the first coordinate alone
gives the graded listener on the marginal prior, since the meaning carries no information about
the second coordinate. -/
theorem gradedListener_map_fst {V : Type*} [MeasurableSpace V] (μ : Measure (W × V))
    (m : U → W → ℝ≥0∞) (hm : ∀ u, Measurable (m u)) (u : U) :
    (gradedListener μ (fun u p ↦ m u p.1) u).map Prod.fst =
      gradedListener (μ.map Prod.fst) m u := by
  have key : (μ.withDensity fun p ↦ m u p.1).map Prod.fst = (μ.map Prod.fst).withDensity (m u) :=
    Measure.map_withDensity_comp (hm u) measurable_fst
  have huniv : (μ.withDensity fun p ↦ m u p.1) Set.univ =
      (μ.map Prod.fst).withDensity (m u) Set.univ := by
    rw [← key, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  simp only [gradedListener_apply, ProbabilityTheory.cond, Measure.restrict_univ,
    Measure.map_smul _ measurable_fst.aemeasurable, key, huniv]

section Boolean

variable [DiscreteMeasurableSpace W] (μ : Measure W) (sem : U → Set W)

theorem literalListener_apply_singleton {u : U} {w : W} (h : w ∈ sem u) :
    literalListener μ sem u {w} = (μ (sem u))⁻¹ * μ {w} := by
  rw [literalListener_apply, cond_apply .of_discrete,
    Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)]

theorem literalListener_apply_singleton_of_notMem {u : U} {w : W} (h : w ∉ sem u) :
    literalListener μ sem u {w} = 0 := by
  rw [literalListener_apply, cond_apply .of_discrete, Set.inter_comm,
    Set.singleton_inter_eq_empty.mpr h, measure_empty, mul_zero]

/-- A tautology leaves a probability prior unchanged. -/
theorem literalListener_apply_singleton_of_eq_univ [IsProbabilityMeasure μ] {u : U}
    (h : sem u = Set.univ) (w : W) : literalListener μ sem u {w} = μ {w} := by
  rw [literalListener_apply_singleton μ sem (by rw [h]; exact Set.mem_univ w), h, measure_univ,
    inv_one, one_mul]

/-- An utterance true at one state only puts all its mass there. -/
theorem literalListener_apply_singleton_of_eq_singleton [IsFiniteMeasure μ] {u : U} {w : W}
    (h : sem u = {w}) (hμ : μ {w} ≠ 0) : literalListener μ sem u {w} = 1 := by
  rw [literalListener_apply_singleton μ sem (by rw [h]; exact Set.mem_singleton w), h,
    ENNReal.inv_mul_cancel hμ (measure_ne_top _ _)]

omit [DiscreteMeasurableSpace W] in
/-- The literal listener of an utterance with a positive-mass extension is a probability
measure. -/
theorem literalListener_apply_univ [IsFiniteMeasure μ] {u : U} (h : μ (sem u) ≠ 0) :
    literalListener μ sem u Set.univ = 1 := by
  rw [literalListener_apply]
  have := cond_isProbabilityMeasure (μ := μ) h
  exact measure_univ

/-- The literal listener puts mass on a state exactly when the utterance is true there and the
state has positive prior. -/
theorem literalListener_apply_singleton_ne_zero_iff [IsFiniteMeasure μ] (u : U) (w : W) :
    literalListener μ sem u {w} ≠ 0 ↔ w ∈ sem u ∧ μ {w} ≠ 0 := by
  by_cases h : w ∈ sem u
  · rw [literalListener_apply_singleton μ sem h]
    exact ⟨fun h' ↦ ⟨h, (mul_ne_zero_iff.mp h').2⟩,
      fun h' ↦ mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) h'.2⟩
  · rw [literalListener_apply_singleton_of_notMem μ sem h]
    exact iff_of_false (fun h' ↦ h' rfl) fun h' ↦ h h'.1

/-- A relabelling of the states that carries one prior and extension to another carries the
literal listener along. -/
theorem literalListener_apply_singleton_of_equiv {W' U' : Type*} [MeasurableSpace W']
    [DiscreteMeasurableSpace W'] [MeasurableSpace U'] [Countable U'] [MeasurableSingletonClass U']
    [Fintype W] [Fintype W'] (e : W ≃ W') {μ : Measure W} {μ' : Measure W'} {sem : U → Set W}
    {sem' : U' → Set W'} {u : U} {u' : U'} (hμ : ∀ w, μ' {e w} = μ {w})
    (hsem : ∀ w, e w ∈ sem' u' ↔ w ∈ sem u) (w : W) :
    literalListener μ' sem' u' {e w} = literalListener μ sem u {w} := by
  rw [← gradedListener_indicator, ← gradedListener_indicator]
  refine gradedListener_apply_singleton_of_equiv e hμ (fun w ↦ ?_) w
  by_cases h : w ∈ sem u
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hsem w).2 h), Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt (hsem w).1 h)]

end Boolean

/-- On natural-number weights and likelihoods the graded literal listener is the weighted
likelihood over its total. -/
theorem gradedListener_natCast_real_singleton [Fintype W] [MeasurableSingletonClass W]
    (w : W → ℕ) (lik : U → W → ℕ) (u : U) (x : W) :
    (gradedListener (Measure.ofWeights (w ·)) (fun u x ↦ (lik u x : ℝ≥0∞)) u).real {x}
      = (lik u x * w x : ℝ) / ∑ x', (lik u x' * w x' : ℝ) := by
  rw [measureReal_def, gradedListener_apply_singleton, ENNReal.toReal_div,
    ENNReal.toReal_sum fun _ _ ↦ ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)]
  simp [ENNReal.toReal_mul]

end LiteralListener

variable [Countable W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U]

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

end ScoreSpeaker

/-! #### The informativity speaker

The speaker of eqs. 2/6–7 is the score speaker at Frank and Goodman's utility, the log of the
literal listener's mass at the state less the cost, scaled by the rationality. A cost is a real
number, entering the speaker's weight as `exp (-(α * C u))`, so every weight is positive and
finite and no hypothesis on the cost is needed. -/

/-- The utility of an utterance at a state is the log of the listener's mass there, less the
cost. -/
noncomputable def utility (L : Kernel U W) (C : U → ℝ) (w : W) (u : U) : EReal :=
  ENNReal.log (L u {w}) - C u

/-- The pragmatic speaker (eqs. 2/6–7) is the softmax of the utility at rationality `α`. -/
noncomputable def speaker (α : ℝ) (C : U → ℝ) (L : Kernel U W) : Kernel W U :=
  speakerOfScore fun w u ↦ utility L C w u * α

instance (α : ℝ) (C : U → ℝ) (L : Kernel U W) : IsFiniteKernel (speaker α C L) :=
  inferInstanceAs (IsFiniteKernel (speakerOfScore _))

theorem ofReal_exp_neg_rpow (c α : ℝ) :
    ENNReal.ofReal (Real.exp (-c)) ^ α = ENNReal.ofReal (Real.exp (-(α * c))) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 2; ring

omit [Countable W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U] in
theorem exp_utility_mul (L : Kernel U W) [IsFiniteKernel L] (C : U → ℝ) (α : ℝ) (w : W) (u : U) :
    EReal.exp (utility L C w u * α) = L u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) := by
  rw [EReal.exp_mul, utility, sub_eq_add_neg, ← EReal.coe_neg, EReal.exp_add, ENNReal.exp_log,
    EReal.exp_coe, ENNReal.mul_rpow_of_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ofReal_exp_neg_rpow]

omit [MeasurableSingletonClass U] in
/-- The speaker in the power-weight form, `L u {w} ^ α` times the cost weight `exp (-(α * C u))`. -/
theorem speaker_eq_ofWeights (α : ℝ) (C : U → ℝ) (L : Kernel U W) [IsFiniteKernel L] :
    speaker α C L =
      Kernel.ofWeights fun w u ↦ L u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) := by
  unfold speaker speakerOfScore
  simp_rw [exp_utility_mul]

@[simp] theorem speaker_apply_singleton (α : ℝ) (C : U → ℝ) (L : Kernel U W) [IsFiniteKernel L]
    (w : W) (u : U) :
    speaker α C L w {u} = L u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))
      / ∑ u', L u' {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) := by
  rw [speaker_eq_ofWeights, Kernel.ofWeights_apply_singleton]

/-- At zero cost the speaker's weights are the listener's masses to the power `α`. -/
theorem speaker_zero_apply_singleton (α : ℝ) (L : Kernel U W) [IsFiniteKernel L] (w : W) (u : U) :
    speaker α 0 L w {u} = L u {w} ^ α / ∑ u', L u' {w} ^ α := by
  rw [speaker_apply_singleton]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]

variable {α : ℝ} {C : U → ℝ} {L : Kernel U W} {w : W} {u : U}

private theorem ofReal_exp_ne_zero (x : ℝ) : ENNReal.ofReal (Real.exp x) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

omit [Countable W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U] in
private theorem weight_ne_top [IsFiniteKernel L] (hα : 0 ≤ α) (C : U → ℝ) (u : U) (w : W) :
    L u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα (measure_ne_top _ _)) ENNReal.ofReal_ne_top

private theorem rpow_ne_zero_of_ne_zero {x : ℝ≥0∞} (hα : 0 ≤ α) (hx : x ≠ 0) : x ^ α ≠ 0 := by
  rw [ne_eq, ENNReal.rpow_eq_zero_iff, not_or]
  exact ⟨fun h ↦ hx h.1, fun h ↦ absurd hα (not_le.mpr h.2)⟩

omit [Countable W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U] in
private theorem weight_ne_zero (hα : 0 ≤ α) (C : U → ℝ) (h : L u {w} ≠ 0) :
    L u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) ≠ 0 :=
  mul_ne_zero (rpow_ne_zero_of_ne_zero hα h) (ofReal_exp_ne_zero _)

/-- Relabelling the utterances carries the speaker along, with the cost relabelled with them. A
listener that treats `τ v` at `w'` as the other treats `v` at `w` makes the speaker at `w'` produce
`τ u` as the other produces `u` at `w`. -/
theorem speaker_apply_singleton_of_equiv {W' U' : Type*} [MeasurableSpace W'] [MeasurableSpace U']
    [Countable W'] [MeasurableSingletonClass W'] [Fintype U'] [MeasurableSingletonClass U']
    (τ : U ≃ U') (α : ℝ) (C : U' → ℝ) {L : Kernel U W} [IsFiniteKernel L] {L' : Kernel U' W'}
    [IsFiniteKernel L'] {w : W} {w' : W'} (h : ∀ v, L' (τ v) {w'} = L v {w}) (u : U) :
    speaker α C L' w' {τ u} = speaker α (C ∘ τ) L w {u} := by
  rw [speaker_apply_singleton, speaker_apply_singleton, h, ← τ.sum_comp]
  simp only [h, Function.comp_apply]

omit [MeasurableSingletonClass U] in
/-- The speaker is a probability kernel whenever every state has a true utterance. -/
theorem isMarkovKernel_speaker (hα : 0 ≤ α) (C : U → ℝ) (L : Kernel U W) [IsFiniteKernel L]
    (h0 : ∀ w, ∃ u, L u {w} ≠ 0) : IsMarkovKernel (speaker α C L) := by
  rw [speaker_eq_ofWeights]
  exact Kernel.isMarkovKernel_ofWeights (fun w ↦ (h0 w).imp fun u hu ↦ weight_ne_zero hα C hu)
    fun w u ↦ weight_ne_top hα C u w

/-- A literally false utterance is never produced (positive rationality). -/
theorem speaker_apply_singleton_eq_zero (hα : 0 < α) (h : L u {w} = 0) :
    speaker α C L w {u} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (by
    show EReal.exp (utility L C w u * α) = 0
    rw [utility, h, ENNReal.log_zero, EReal.bot_sub, EReal.bot_mul_coe_of_pos hα, EReal.exp_bot])

/-- A literally true utterance is produced with positive mass. -/
theorem speaker_apply_singleton_ne_zero [IsFiniteKernel L] (hα : 0 ≤ α) (h : L u {w} ≠ 0) :
    speaker α C L w {u} ≠ 0 := by
  rw [speaker_eq_ofWeights]
  exact Kernel.ofWeights_apply_singleton_ne_zero (weight_ne_zero hα C h)
    fun u' ↦ weight_ne_top hα C u' w

theorem speaker_apply_singleton_ne_zero_iff [IsFiniteKernel L] (hα : 0 < α) :
    speaker α C L w {u} ≠ 0 ↔ L u {w} ≠ 0 :=
  ⟨fun h h' ↦ h (speaker_apply_singleton_eq_zero hα h'), speaker_apply_singleton_ne_zero hα.le⟩

/-- A state with a unique applicable utterance produces it with certainty. -/
theorem speaker_apply_singleton_eq_one [IsFiniteKernel L] (hα : 0 < α) (h : L u {w} ≠ 0)
    (hother : ∀ u' ≠ u, L u' {w} = 0) : speaker α C L w {u} = 1 := by
  rw [speaker_apply_singleton, Finset.sum_eq_single u
    (fun u' _ hu' ↦ by rw [hother u' hu', ENNReal.zero_rpow_of_pos hα, zero_mul])
    (fun hu ↦ absurd (Finset.mem_univ u) hu)]
  exact ENNReal.div_self (weight_ne_zero hα.le C h) (weight_ne_top hα.le C u w)

/-- On reals a speaker share is the weighted listener value over the row's total. -/
theorem speaker_real_singleton [IsFiniteKernel L] (hα : 0 ≤ α) (u : U) :
    (speaker α C L w).real {u}
      = (L u {w} ^ α).toReal * Real.exp (-(α * C u))
        / ∑ u', (L u' {w} ^ α).toReal * Real.exp (-(α * C u')) := by
  rw [measureReal_def, speaker_apply_singleton, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_sum fun u' _ ↦ weight_ne_top hα C u' w]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- At zero cost a speaker share on reals is the listener's mass to the power `α` over the row's
total. -/
theorem speaker_zero_real_singleton [IsFiniteKernel L] (hα : 0 ≤ α) (u : U) :
    (speaker α 0 L w).real {u} = (L u {w} ^ α).toReal / ∑ u', (L u' {w} ^ α).toReal := by
  rw [speaker_real_singleton hα]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, mul_one]

omit [MeasurableSingletonClass U] in
/-- A speaker row has total mass at most one. -/
theorem speaker_apply_univ_le_one (α : ℝ) (C : U → ℝ) (L : Kernel U W) (w : W) :
    speaker α C L w Set.univ ≤ 1 :=
  Kernel.ofWeights_apply_univ_le_one _ w

omit [MeasurableSingletonClass U] in
/-- Speaker shares are at most one. -/
theorem speaker_real_singleton_le_one (α : ℝ) (C : U → ℝ) (L : Kernel U W) (w : W) (u : U) :
    (speaker α C L w).real {u} ≤ 1 := by
  rw [measureReal_def, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    ((measure_mono (Set.subset_univ _)).trans (Kernel.ofWeights_apply_univ_le_one _ w))

/-- Row-preference of the speaker reduces to comparing the weighted listener values; the
normalization cancels. -/
theorem speaker_real_singleton_lt_iff [IsFiniteKernel L] (hα : 0 ≤ α) (h0 : ∃ u, L u {w} ≠ 0)
    {u u' : U} :
    (speaker α C L w).real {u} < (speaker α C L w).real {u'} ↔
      L u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))
        < L u' {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) := by
  rw [speaker_eq_ofWeights]
  exact Kernel.ofWeights_real_singleton_lt_iff w
    (fun h ↦ let ⟨u₀, hu₀⟩ := h0
      weight_ne_zero hα C hu₀ (Finset.sum_eq_zero_iff.mp h u₀ (Finset.mem_univ _)))
    (ENNReal.sum_ne_top.mpr fun u _ ↦ weight_ne_top hα C u w)

/-- With Boolean meanings, a state whose only true utterance is `u` produces `u` with
certainty at any prior giving the state positive mass. -/
theorem speaker_literalListener_eq_one [DiscreteMeasurableSpace W] (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) (hμ : μ {w} ≠ 0)
    (hmem : w ∈ sem u) (hother : ∀ u' ≠ u, w ∉ sem u') :
    speaker α C (literalListener μ sem) w {u} = 1 :=
  speaker_apply_singleton_eq_one hα
    (by
      rw [literalListener_apply_singleton μ sem hmem]
      exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hμ)
    fun u' hu' ↦ literalListener_apply_singleton_of_notMem μ sem (hother u' hu')

/-- With Boolean meanings the speaker produces an utterance at a state exactly when it is true
there and the state has positive prior. -/
theorem speaker_literalListener_apply_singleton_ne_zero_iff
    [DiscreteMeasurableSpace W] (hα : 0 < α) (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ]
    (sem : U → Set W) (u : U) (w : W) :
    speaker α C (literalListener μ sem) w {u} ≠ 0
      ↔ w ∈ sem u ∧ μ {w} ≠ 0 := by
  rw [speaker_apply_singleton_ne_zero_iff hα,
    literalListener_apply_singleton_ne_zero_iff μ sem u w]

/-- With Boolean meanings the speaker sees a state only through the utterances true at it, so two
states of positive prior verifying the same utterances have the same production row. -/
theorem speaker_literalListener_congr [DiscreteMeasurableSpace W] (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W)
    {w w' : W} (hw : μ {w} ≠ 0) (hw' : μ {w'} ≠ 0) (h : ∀ u, w ∈ sem u ↔ w' ∈ sem u) :
    speaker α C (literalListener μ sem) w'
      = speaker α C (literalListener μ sem) w := by
  rw [speaker_eq_ofWeights]
  refine Kernel.ofWeights_apply_eq_of_mul (c := (μ {w'} / μ {w}) ^ α)
    (rpow_ne_zero_of_ne_zero hα.le (ENNReal.div_ne_zero.mpr ⟨hw', measure_ne_top _ _⟩))
    (ENNReal.rpow_ne_top_of_nonneg hα.le (ENNReal.div_ne_top (measure_ne_top _ _) hw))
    fun u ↦ ?_
  by_cases hu : w ∈ sem u
  · rw [literalListener_apply_singleton μ sem hu,
      literalListener_apply_singleton μ sem ((h u).mp hu), mul_right_comm,
      ← ENNReal.mul_rpow_of_nonneg _ _ hα.le, mul_assoc,
      ENNReal.mul_div_cancel hw (measure_ne_top _ _)]
  · rw [literalListener_apply_singleton_of_notMem μ sem hu,
      literalListener_apply_singleton_of_notMem μ sem (mt (h u).mpr hu),
      ENNReal.zero_rpow_of_pos hα, zero_mul, zero_mul]

/-- With Boolean meanings the prior cancels from the speaker, which at a state of positive prior
weights each true utterance by its extension's mass to the power `-α` and by its cost. -/
theorem speaker_literalListener_apply_singleton [DiscreteMeasurableSpace W] (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) (hw : μ {w} ≠ 0) (u : U) :
    speaker α C (literalListener μ sem) w {u}
      = (sem u).indicator (fun _ ↦ (μ (sem u))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))) w
        / ∑ u', (sem u').indicator
            (fun _ ↦ (μ (sem u'))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C u')))) w := by
  have key : ∀ v, (literalListener μ sem) v {w} ^ α
        * ENNReal.ofReal (Real.exp (-(α * C v)))
      = μ {w} ^ α * (sem v).indicator
          (fun _ ↦ (μ (sem v))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C v)))) w := fun v ↦ by
    by_cases hv : w ∈ sem v
    · rw [literalListener_apply_singleton μ sem hv, Set.indicator_of_mem hv,
        ENNReal.mul_rpow_of_nonneg _ _ hα.le]
      ring
    · rw [literalListener_apply_singleton_of_notMem μ sem hv,
        Set.indicator_of_notMem hv, ENNReal.zero_rpow_of_pos hα, zero_mul, mul_zero]
  rw [speaker_apply_singleton, key, Finset.sum_congr rfl fun v _ ↦ key v, ← Finset.mul_sum,
    ENNReal.mul_div_mul_left _ _ (rpow_ne_zero_of_ne_zero hα.le hw)
      (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))]

/-- With Boolean meanings a state verifying more utterances produces each of its true utterances
less, since the prior cancels from the speaker and only the inclusion of the true utterances
matters. -/
theorem speaker_literalListener_le_of_subset [DiscreteMeasurableSpace W] (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) {w w' : W}
    (hw : μ {w} ≠ 0) (hsub : ∀ u, w ∈ sem u → w' ∈ sem u) {u : U} (hu : w ∈ sem u) :
    speaker α C (literalListener μ sem) w' {u}
      ≤ speaker α C (literalListener μ sem) w {u} := by
  rcases eq_or_ne (μ {w'}) 0 with hw' | hw'
  · rw [speaker_apply_singleton_eq_zero hα (not_not.mp fun h ↦
      ((literalListener_apply_singleton_ne_zero_iff μ sem u w').mp h).2 hw')]
    exact zero_le
  rw [speaker_literalListener_apply_singleton hα C μ sem hw,
    speaker_literalListener_apply_singleton hα C μ sem hw',
    Set.indicator_of_mem hu, Set.indicator_of_mem (hsub u hu)]
  refine ENNReal.div_le_div_left (Finset.sum_le_sum fun v _ ↦ ?_) _
  by_cases hv : w ∈ sem v
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hsub v hv)]
  · rw [Set.indicator_of_notMem hv]; exact zero_le


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
/-- As rationality grows, the speaker puts all its mass on the utterance whose listener mass,
discounted by its cost, is greatest at `w`, so the fully rational speaker maximizes the
utility. -/
theorem tendsto_speaker_real_singleton_atTop [IsFiniteKernel L] (hu : L u {w} ≠ 0)
    (hmax : ∀ u' ≠ u, (L u' {w}).toReal * Real.exp (-C u') < (L u {w}).toReal * Real.exp (-C u)) :
    Tendsto (fun α ↦ (speaker α C L w).real {u}) atTop (𝓝 1) := by
  classical
  set m : U → ℝ := fun v ↦ (L v {w}).toReal * Real.exp (-C v)
  have hm0 (v : U) : 0 ≤ m v := mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hmu : 0 < m u := mul_pos (ENNReal.toReal_pos hu (measure_ne_top _ _)) (Real.exp_pos _)
  have hterm (α : ℝ) (v : U) : (L v {w} ^ α).toReal * Real.exp (-(α * C v)) = m v ^ α := by
    rw [← ENNReal.toReal_rpow, Real.mul_rpow ENNReal.toReal_nonneg (Real.exp_pos _).le,
      ← Real.exp_mul]
    congr 2; ring
  have hform : ∀ᶠ α in atTop, (∑ v, (m v / m u) ^ α)⁻¹ = (speaker α C L w).real {u} := by
    filter_upwards [eventually_ge_atTop 0] with α hα
    have hsum : ∑ v, (m v / m u) ^ α = (∑ v, m v ^ α) / m u ^ α := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun v _ ↦ Real.div_rpow (hm0 v) hmu.le α
    rw [speaker_real_singleton hα, hterm]
    simp_rw [hterm]
    rw [hsum, inv_div]
  have hlim : Tendsto (fun α : ℝ ↦ ∑ v, (m v / m u) ^ α) atTop
      (𝓝 (∑ v, if v = u then (1 : ℝ) else 0)) := by
    refine tendsto_finsetSum _ fun v _ ↦ ?_
    by_cases hv : v = u
    · subst hv
      have h1 : HPow.hPow (m v / m v) = fun _ : ℝ ↦ (1 : ℝ) :=
        funext fun α ↦ by rw [div_self hmu.ne', Real.one_rpow]
      rw [h1]; simp
    · have hlt : m v / m u < 1 := (div_lt_one hmu).2 (hmax v hv)
      simpa only [hv, ite_false] using
        tendsto_rpow_atTop_of_base_lt_one _ (by linarith [div_nonneg (hm0 v) hmu.le]) hlt
  rw [Finset.sum_ite_eq' Finset.univ u, ite_eq_left (Finset.mem_univ u)] at hlim
  simpa using (hlim.inv₀ one_ne_zero).congr' hform

/-- With Boolean meanings and a constant cost, a state two utterances both fit produces the
utterance with the smaller extension more often, since informativity is the inverse of extension
mass. -/
theorem speaker_literalListener_real_singleton_lt_iff [DiscreteMeasurableSpace W]
    (hα : 0 < α) (c : ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) (hμ : μ {w} ≠ 0)
    {u u' : U} (hu : w ∈ sem u) (hu' : w ∈ sem u') :
    (speaker α (fun _ ↦ c) (literalListener μ sem) w).real {u}
        < (speaker α (fun _ ↦ c) (literalListener μ sem) w).real {u'}
      ↔ μ (sem u') < μ (sem u) := by
  have hne : literalListener μ sem u {w} ≠ 0 := by
    rw [literalListener_apply_singleton μ sem hu]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hμ
  have key : ∀ {a b k : ℝ≥0∞}, k ≠ 0 → k ≠ ∞ → (a * k < b * k ↔ a < b) := fun h0 htop ↦
    ⟨fun h ↦ lt_of_not_ge fun hab ↦ absurd h (not_lt.mpr (mul_le_mul' hab le_rfl)),
      ENNReal.mul_lt_mul_left h0 htop⟩
  rw [speaker_real_singleton_lt_iff hα.le ⟨u, hne⟩,
    key (ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top, ENNReal.rpow_lt_rpow_iff hα,
    literalListener_apply_singleton μ sem hu,
    literalListener_apply_singleton μ sem hu', key hμ (measure_ne_top _ _),
    ENNReal.inv_lt_inv]

/-! #### Pragmatic listeners -/

section Listener

variable [StandardBorelSpace W] [Nonempty W]

/-- The pragmatic listener (eq. 3) is the Bayesian inverse of a speaker against the prior. -/
noncomputable def pragmaticListener (S : Kernel W U) [IsFiniteKernel S] (μ : Measure W)
    [IsFiniteMeasure μ] : Kernel U W :=
  S†μ

section General

variable {S : Kernel W U} [IsFiniteKernel S] {μ : Measure W} [IsFiniteMeasure μ]

instance : IsMarkovKernel (pragmaticListener S μ) := inferInstanceAs (IsMarkovKernel (S†μ))

omit [Countable W] [Fintype U] in
/-- At an utterance of positive marginal the listener's mass on a state is its prior times the
speaker's production there, over the marginal. -/
theorem pragmaticListener_apply_singleton {u : U} (hu : (S ∘ₘ μ) {u} ≠ 0) (w : W) :
    pragmaticListener S μ u {w} = μ {w} * S w {u} / (S ∘ₘ μ) {u} :=
  posterior_apply_singleton S μ hu w

omit [Countable W] [Fintype U] in
/-- A state at which the utterance is never produced receives no posterior mass. -/
theorem pragmaticListener_apply_singleton_eq_zero {u : U} (hu : (S ∘ₘ μ) {u} ≠ 0) {w : W}
    (hw : S w {u} = 0) : pragmaticListener S μ u {w} = 0 := by
  rw [pragmaticListener_apply_singleton hu, hw, mul_zero, ENNReal.zero_div]

omit [Countable W] [Fintype U] in
/-- The listener puts mass on a state exactly when it has positive prior and the speaker produces
the utterance there. -/
theorem pragmaticListener_apply_singleton_ne_zero_iff {u : U} (hu : (S ∘ₘ μ) {u} ≠ 0) (w : W) :
    pragmaticListener S μ u {w} ≠ 0 ↔ μ {w} ≠ 0 ∧ S w {u} ≠ 0 :=
  posterior_apply_singleton_ne_zero_iff S μ hu w

omit [Countable W] [Fintype U] in
/-- Comparing the listener's masses on finite events reduces to comparing prior-weighted speaker
productions. -/
theorem pragmaticListener_real_finset_lt_iff {u : U} (hu : (S ∘ₘ μ) {u} ≠ 0)
    (E₁ E₂ : Finset W) :
    (pragmaticListener S μ u).real ↑E₁ < (pragmaticListener S μ u).real ↑E₂
      ↔ (∑ w ∈ E₁, μ.real {w} * (S w).real {u}) < ∑ w ∈ E₂, μ.real {w} * (S w).real {u} :=
  posterior_real_finset_lt_iff S μ hu E₁ E₂

omit [Countable W] [Fintype U] in
/-- At a prior giving every state the same positive mass, listener preference between two
states is speaker preference between them, since the prior and the marginal cancel. -/
theorem pragmaticListener_real_lt_iff (hμeq : ∀ w w', μ {w} = μ {w'}) (hμ0 : ∀ w, μ {w} ≠ 0)
    {u : U} {w₀ : W} (hs : S w₀ {u} ≠ 0) {w₁ w₂ : W} :
    (pragmaticListener S μ u).real {w₁} < (pragmaticListener S μ u).real {w₂}
      ↔ (S w₁).real {u} < (S w₂).real {u} :=
  posterior_real_singleton_lt_iff_of_eq _ _ (comp_apply_singleton_ne_zero _ _ (hμ0 w₀) hs)
    (hμeq w₁ w₂) (hμ0 w₁)

omit [Countable W] [Fintype U] in
/-- A relabelling of states and utterances that carries one speaker and prior to another carries
the listener along. -/
theorem pragmaticListener_apply_singleton_of_equiv [Fintype W] {W' U' : Type*}
    [MeasurableSpace W'] [MeasurableSpace U'] [MeasurableSingletonClass U'] [Fintype W']
    [MeasurableSingletonClass W'] [StandardBorelSpace W'] [Nonempty W'] {S' : Kernel W' U'}
    [IsFiniteKernel S'] {μ' : Measure W'} [IsFiniteMeasure μ'] (e : W ≃ W') {u : U} {u' : U'}
    (hμ : ∀ w, μ' {e w} = μ {w}) (hS : ∀ w, S' (e w) {u'} = S w {u})
    (hu : (S ∘ₘ μ) {u} ≠ 0) (w : W) :
    pragmaticListener S' μ' u' {e w} = pragmaticListener S μ u {w} :=
  posterior_apply_singleton_of_equiv _ _ e hμ hS hu w

end General

/-- With Boolean meanings, hearing an utterance rules out every state it does not fit, once some
state it fits has prior mass. -/
theorem pragmaticListener_literalListener_apply_singleton_of_notMem [DiscreteMeasurableSpace W]
    (α : ℝ) (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (hα : 0 < α)
    (sem : U → Set W) {u : U} {w w' : W} (hw : w ∉ sem u) (hw' : w' ∈ sem u) (hμ : μ {w'} ≠ 0) :
    pragmaticListener (speaker α C (literalListener μ sem)) μ u {w} = 0 := by
  have hS : speaker α C (literalListener μ sem) w' {u} ≠ 0 :=
    speaker_apply_singleton_ne_zero hα.le (by
      rw [literalListener_apply_singleton μ sem hw']
      exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hμ)
  exact pragmaticListener_apply_singleton_eq_zero (comp_apply_singleton_ne_zero _ _ hμ hS)
    (speaker_apply_singleton_eq_zero hα (literalListener_apply_singleton_of_notMem μ sem hw))

section Latent

variable {Λ : Type*} [MeasurableSpace Λ] [StandardBorelSpace Λ] [Nonempty Λ]
  [MeasurableSingletonClass Λ] {S : Kernel (W × Λ) U} [IsFiniteKernel S] {μ : Measure (W × Λ)}
  [IsFiniteMeasure μ]

omit [Countable W] [Fintype U] in
/-- The state marginal of the listener over a latent is positive at a state exactly when some
latent pairs a positive prior with a positive production. -/
theorem pragmaticListener_fst_apply_singleton_ne_zero_iff [Fintype Λ] {u : U}
    (hu : (S ∘ₘ μ) {u} ≠ 0) (w : W) :
    (pragmaticListener S μ u).fst {w} ≠ 0 ↔ ∃ l, μ {(w, l)} ≠ 0 ∧ S (w, l) {u} ≠ 0 := by
  rw [Measure.fst_apply_singleton, ne_eq, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, not_forall,
    pragmaticListener_apply_singleton_ne_zero_iff hu]

omit [Countable W] [Fintype U] in
/-- At equal priors the listener's state marginal prefers the state with the greater production
summed over the latent. -/
theorem pragmaticListener_fst_real_lt_iff [Fintype Λ] (hμeq : ∀ p q : W × Λ, μ {p} = μ {q})
    (hμ0 : ∀ p : W × Λ, μ {p} ≠ 0) {u : U} {p₀ : W × Λ} (hs : S p₀ {u} ≠ 0) {w₁ w₂ : W} :
    (pragmaticListener S μ u).fst.real {w₁} < (pragmaticListener S μ u).fst.real {w₂}
      ↔ (∑ l, (S (w₁, l)).real {u}) < ∑ l, (S (w₂, l)).real {u} := by
  have key : ∀ w : W, (∑ l, μ.real {(w, l)} * (S (w, l)).real {u})
      = μ.real {p₀} * ∑ l, (S (w, l)).real {u} := fun w ↦ by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by
      rw [show μ.real {(w, l)} = μ.real {p₀} by rw [measureReal_def, measureReal_def, hμeq]]
  rw [pragmaticListener, posterior_fst_real_lt_iff _ _
    (comp_apply_singleton_ne_zero _ _ (hμ0 p₀) hs), key, key, mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real {p₀} from ENNReal.toReal_pos (hμ0 p₀) (measure_ne_top _ _))]

omit [Countable W] [Fintype U] in
/-- At equal priors the listener's latent marginal prefers the latent with the greater
production summed over the states. -/
theorem pragmaticListener_snd_real_lt_iff [Fintype W] [Countable Λ]
    (hμeq : ∀ p q : W × Λ, μ {p} = μ {q}) (hμ0 : ∀ p : W × Λ, μ {p} ≠ 0) {u : U} {p₀ : W × Λ}
    (hs : S p₀ {u} ≠ 0) {l₁ l₂ : Λ} :
    (pragmaticListener S μ u).snd.real {l₁} < (pragmaticListener S μ u).snd.real {l₂}
      ↔ (∑ w, (S (w, l₁)).real {u}) < ∑ w, (S (w, l₂)).real {u} := by
  have key : ∀ l : Λ, (∑ w, μ.real {(w, l)} * (S (w, l)).real {u})
      = μ.real {p₀} * ∑ w, (S (w, l)).real {u} := fun l ↦ by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ ↦ by
      rw [show μ.real {(w, l)} = μ.real {p₀} by rw [measureReal_def, measureReal_def, hμeq]]
  rw [pragmaticListener, posterior_snd_real_lt_iff _ _
    (comp_apply_singleton_ne_zero _ _ (hμ0 p₀) hs), key, key, mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real {p₀} from ENNReal.toReal_pos (hμ0 p₀) (measure_ne_top _ _))]

omit [Countable W] [Fintype U] in
/-- On reals the state marginal of the listener over a product prior is the prior at the state
times the latent-averaged production, over the observation marginal. -/
theorem pragmaticListener_fst_real_singleton [Fintype Λ] (μW : Measure W) [IsFiniteMeasure μW]
    (ν : Measure Λ) [IsFiniteMeasure ν] {u : U} (hu : (S ∘ₘ μW.prod ν) {u} ≠ 0) (w : W) :
    (pragmaticListener S (μW.prod ν) u).fst.real {w}
      = μW.real {w} * (∑ l, ν.real {l} * (S (w, l)).real {u}) / (S ∘ₘ μW.prod ν).real {u} := by
  rw [pragmaticListener, posterior_fst_real_singleton _ _ hu, Finset.mul_sum]
  simp_rw [Measure.prod_real_singleton, mul_assoc]

omit [Countable W] [Fintype U] in
/-- A pair producing the utterance with certainty outweighs any event of smaller total prior
mass, when no pair produces it with probability above one. -/
theorem pragmaticListener_real_lt_of_certain [Countable Λ] {u : U} {E₁ E₂ : Finset (W × Λ)}
    {p₀ : W × Λ} (hp₀ : p₀ ∈ E₂) (hle : ∀ p, (S p).real {u} ≤ 1) (hs : S p₀ {u} = 1)
    (hlt : (∑ p ∈ E₁, μ.real {p}) < μ.real {p₀}) :
    (pragmaticListener S μ u).real ↑E₁ < (pragmaticListener S μ u).real ↑E₂ := by
  have hpos : 0 < μ.real {p₀} := (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg).trans_lt hlt
  rw [pragmaticListener_real_finset_lt_iff (comp_apply_singleton_ne_zero _ _
    (ENNReal.toReal_pos_iff.mp hpos).1.ne' (hs ▸ one_ne_zero))]
  calc ∑ p ∈ E₁, μ.real {p} * (S p).real {u}
      ≤ ∑ p ∈ E₁, μ.real {p} :=
        Finset.sum_le_sum fun p _ ↦ mul_le_of_le_one_right measureReal_nonneg (hle p)
    _ < μ.real {p₀} := hlt
    _ = μ.real {p₀} * (S p₀).real {u} := by
        rw [measureReal_def (μ := S p₀), hs, ENNReal.toReal_one, mul_one]
    _ ≤ ∑ p ∈ E₂, μ.real {p} * (S p).real {u} :=
        Finset.single_le_sum (f := fun p ↦ μ.real {p} * (S p).real {u})
          (fun p _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg) hp₀

end Latent

variable (α : ℝ) (C : U → ℝ) (L : Kernel U W) (μ : Measure W) [IsFiniteMeasure μ]

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
  pragmaticListener (Kernel.deterministic (fun p : W × U ↦ obs p.2) (measurable_obs_snd obs))
    (μ ⊗ₘ speaker α C L)

omit [MeasurableSingletonClass U] [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace U]
  [Nonempty U] [DecidableEq O] [IsFiniteMeasure μ] in
/-- The heard form is distributed as the production marginal. -/
theorem deterministic_comp_compProd_speaker :
    Kernel.deterministic (fun p : W × U ↦ obs p.2) (measurable_obs_snd obs)
        ∘ₘ (μ ⊗ₘ speaker α C L)
      = (speaker α C L ∘ₘ μ).map obs := by
  rw [Measure.deterministic_comp_eq_map, show (fun p : W × U ↦ obs p.2) = obs ∘ Prod.snd from rfl,
    ← Measure.map_map Measurable.of_discrete measurable_snd, ← Measure.snd, Measure.snd_compProd]

omit [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace U] [Nonempty U] [DecidableEq O]
  [IsFiniteMeasure μ] in
/-- A positive-prior state with a positively produced `o`-shaped utterance witnesses a
positive observation marginal. -/
theorem map_comp_speaker_ne_zero [MeasurableSingletonClass O] {w : W} {u : U} {o : O}
    (hμ : μ {w} ≠ 0) (hu : obs u = o) (hs : speaker α C L w {u} ≠ 0) :
    ((speaker α C L ∘ₘ μ).map obs) {o} ≠ 0 := by
  rw [Measure.map_apply Measurable.of_discrete (.singleton o)]
  intro h
  exact comp_apply_singleton_ne_zero _ _ hμ hs
    (measure_mono_null (Set.singleton_subset_iff.mpr (by simp [hu])) h)

variable [MeasurableSingletonClass O]

/-- Exact Bayes for the joint listener at a positive-mass observation. -/
theorem jointListener_apply_singleton {o : O} (ho : ((speaker α C L ∘ₘ μ).map obs) {o} ≠ 0)
    (w : W) (u : U) :
    jointListener α C L μ obs o {(w, u)}
      = (if obs u = o then μ {w} * speaker α C L w {u} else 0)
        / ((speaker α C L ∘ₘ μ).map obs) {o} := by
  rw [jointListener, pragmaticListener_apply_singleton
      (by rwa [deterministic_comp_compProd_speaker]),
    deterministic_comp_compProd_speaker, ← Set.singleton_prod_singleton,
    Measure.compProd_apply_prod (.singleton w) (.singleton u), lintegral_singleton,
    Kernel.deterministic_apply' _ _ (.singleton o)]
  simp only [Set.indicator_apply, Set.mem_singleton_iff]
  split_ifs <;> simp [mul_comm]

/-- The joint listener prefers the state with the greater prior-weighted speaker mass pooled
over the observation's fibre, since the observation's marginal cancels. -/
theorem jointListener_fst_real_lt_iff [Fintype W] {o : O}
    (ho : ((speaker α C L ∘ₘ μ).map obs) {o} ≠ 0) (w₁ w₂ : W) :
    (jointListener α C L μ obs o).fst.real {w₁}
        < (jointListener α C L μ obs o).fst.real {w₂}
      ↔ (∑ u ∈ Finset.univ.filter (obs · = o), μ.real {w₁} * (speaker α C L w₁).real {u})
        < ∑ u ∈ Finset.univ.filter (obs · = o), μ.real {w₂} * (speaker α C L w₂).real {u} := by
  have key : ∀ w : W, (jointListener α C L μ obs o).fst {w}
      = (∑ u ∈ Finset.univ.filter (obs · = o), μ {w} * speaker α C L w {u})
        / ((speaker α C L ∘ₘ μ).map obs) {o} := fun w ↦ by
    rw [Measure.fst_apply_singleton]
    simp_rw [jointListener_apply_singleton α C L μ obs ho, div_eq_mul_inv, ← Finset.sum_mul,
      ← Finset.sum_filter]
  have hne : ∀ w : W,
      (∑ u ∈ Finset.univ.filter (obs · = o), μ {w} * speaker α C L w {u}) ≠ ∞ :=
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
    (ho : ((speaker α C L ∘ₘ μ).map obs) {o} ≠ 0) {u₁ u₂ : U}
    (h₁ : obs u₁ = o) (h₂ : obs u₂ = o) :
    (jointListener α C L μ obs o).snd.real {u₁}
        < (jointListener α C L μ obs o).snd.real {u₂}
      ↔ (∑ w, μ.real {w} * (speaker α C L w).real {u₁})
        < ∑ w, μ.real {w} * (speaker α C L w).real {u₂} := by
  have key : ∀ u, obs u = o → (jointListener α C L μ obs o).snd {u}
      = (∑ w, μ {w} * speaker α C L w {u}) / ((speaker α C L ∘ₘ μ).map obs) {o} :=
    fun u hu ↦ by
      rw [Measure.snd_apply_singleton]
      simp_rw [jointListener_apply_singleton α C L μ obs ho, ite_eq_left hu, div_eq_mul_inv,
        ← Finset.sum_mul]
  have hne : ∀ u : U, (∑ w, μ {w} * speaker α C L w {u}) ≠ ∞ := fun u ↦
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
noncomputable def familySpeaker (L : Λ → Kernel U W) (α : ℝ) (C : U → ℝ) :
    Kernel (W × Λ) U :=
  Kernel.ofFunOfCountable fun p ↦ speaker α C (L p.2) p.1

omit [MeasurableSingletonClass U] in
@[simp] theorem familySpeaker_apply (L : Λ → Kernel U W) (α : ℝ) (C : U → ℝ)
    (p : W × Λ) : familySpeaker L α C p = speaker α C (L p.2) p.1 := rfl

instance (L : Λ → Kernel U W) (α : ℝ) (C : U → ℝ) :
    IsFiniteKernel (familySpeaker L α C) :=
  ⟨⟨1, ENNReal.one_lt_top, fun p ↦ speaker_apply_univ_le_one α C (L p.2) p.1⟩⟩

/-- A member's positively produced utterance at a positive-prior state witnesses a positive
observation marginal for the family speaker. -/
theorem comp_familySpeaker_ne_zero {L : Λ → Kernel U W} {α : ℝ} {C : U → ℝ}
    {μ : Measure (W × Λ)} {w : W} {l : Λ} {u : U} (hμ : μ {(w, l)} ≠ 0)
    (hs : speaker α C (L l) w {u} ≠ 0) : (familySpeaker L α C ∘ₘ μ) {u} ≠ 0 :=
  comp_apply_singleton_ne_zero _ _ hμ (by rwa [familySpeaker_apply])

end Family

end Pipeline

end RSA
