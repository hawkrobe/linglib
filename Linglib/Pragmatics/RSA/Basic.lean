import Linglib.Core.Probability.Kernel.OfWeights
import Linglib.Core.Probability.Kernel.Posterior

/-!
# The Rational Speech Act pipeline on probability kernels

The RSA model ([frank-goodman-2012]; [degen-2023] eqs. 1–4; [franke-bergen-2020]
eqs. 5–22) in mathlib's probability vocabulary. The literal listener is the prior
reweighted by a graded meaning, the speaker is the best response in power-weight form
(`ENNReal.rpow` is total, so falsity needs no signed utilities), and the pragmatic
listeners are mathlib's posterior kernels `κ†μ` — of the speaker, or of the deterministic
observation kernel over the joint of prior and speaker when the listener hears only the form
of the speaker's choice. Rationality, cost, meaning, and prior are arguments, so findings
quantify over them. The uniform-prior Boolean specialization with its decision procedure is
`Linglib.Pragmatics.RSA.Uniform`.

## Main definitions

* `RSA.literalListener` — eq. 1: the prior reweighted by the meaning.
* `RSA.speaker` — eqs. 2/6–7: `ProbabilityTheory.Kernel.ofWeights` of `L ^ α · cost`.
* `RSA.pragmaticListener` — eq. 3: `(speaker α cost L)†μ`.
* `RSA.jointListener` — eqs. 18b/21b: the posterior over (state, choice) given the heard
  form; `.fst` is the state listener, `.snd` the choice posterior.
* `RSA.familySpeaker`, `RSA.familyListener` — state-side latents (eqs. 11–13): the latent
  is a speaker argument and normalization is per latent.

## Main results

* `RSA.jointListener_apply_singleton` — exact Bayes for the joint listener.
* `RSA.jointListener_fst_real_lt_iff`, `RSA.jointListener_snd_real_lt_iff`,
  `RSA.familyListener_fst_real_lt_iff`, `RSA.familyListener_snd_real_lt_iff` — listener
  preference as prior-weighted speaker sums.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### The RSA pipeline -/

namespace RSA

section Pipeline

variable {W U O : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSpace O]

section LiteralListener

variable [Countable U] [MeasurableSingletonClass U]

/-- The literal listener (eq. 1): the prior reweighted by the graded meaning of the
utterance and renormalized. -/
noncomputable def literalListener (μ : Measure W) (m : U → W → ℝ≥0∞) : Kernel U W :=
  Kernel.ofFunOfCountable fun u => (μ.withDensity (m u))[|Set.univ]

theorem literalListener_apply (μ : Measure W) (m : U → W → ℝ≥0∞) (u : U) :
    literalListener μ m u = (μ.withDensity (m u))[|Set.univ] := rfl

/-- On a Boolean meaning the literal listener conditions the prior on the extension. -/
theorem literalListener_indicator [DiscreteMeasurableSpace W] (μ : Measure W)
    (sem : U → Set W) :
    literalListener μ (fun u => (sem u).indicator 1) = Kernel.ofFunOfCountable fun u => μ[|sem u] :=
  Kernel.ext fun u => by
    show (μ.withDensity ((sem u).indicator 1))[|Set.univ] = μ[|sem u]
    rw [withDensity_indicator_one .of_discrete]
    simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.restrict_apply_univ]

theorem literalListener_apply_singleton [Fintype W] [MeasurableSingletonClass W] (μ : Measure W)
    (m : U → W → ℝ≥0∞) (u : U) (w : W) :
    literalListener μ m u {w} = m u w * μ {w} / ∑ w', m u w' * μ {w'} := by
  rw [literalListener_apply, cond_apply MeasurableSet.univ, Set.univ_inter,
    withDensity_apply _ (.singleton w), lintegral_singleton, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_fintype, ENNReal.div_eq_inv_mul]

theorem literalListener_indicator_apply_singleton [DiscreteMeasurableSpace W] (μ : Measure W)
    (sem : U → Set W) {u : U} {w : W} (h : w ∈ sem u) :
    literalListener μ (fun u => (sem u).indicator 1) u {w} = (μ (sem u))⁻¹ * μ {w} := by
  rw [literalListener_indicator, Kernel.ofFunOfCountable_apply, cond_apply .of_discrete,
    Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)]

theorem literalListener_indicator_apply_singleton_of_notMem [DiscreteMeasurableSpace W]
    (μ : Measure W) (sem : U → Set W) {u : U} {w : W} (h : w ∉ sem u) :
    literalListener μ (fun u => (sem u).indicator 1) u {w} = 0 := by
  rw [literalListener_indicator, Kernel.ofFunOfCountable_apply, cond_apply .of_discrete,
    Set.inter_comm, Set.singleton_inter_eq_empty.mpr h, measure_empty, mul_zero]

/-- On a finite-mass extension the literal listener is a subprobability at members. -/
theorem literalListener_indicator_apply_singleton_le_one [DiscreteMeasurableSpace W]
    (μ : Measure W) (sem : U → Set W) {u : U} (hfin : μ (sem u) ≠ ∞) {w : W} (h : w ∈ sem u) :
    literalListener μ (fun u => (sem u).indicator 1) u {w} ≤ 1 := by
  rw [literalListener_indicator_apply_singleton μ sem h]
  rcases eq_or_ne (μ (sem u)) 0 with h0 | h0
  · rw [measure_mono_null (Set.singleton_subset_iff.mpr h) h0, mul_zero]
    exact zero_le_one
  · rw [ENNReal.inv_mul_le_iff h0 hfin, mul_one]
    exact measure_mono (Set.singleton_subset_iff.mpr h)

end LiteralListener

variable [Countable W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U]

theorem weight_rpow_ne_zero {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hx : x ≠ 0) :
    x ^ α ≠ 0 := by
  rw [ne_eq, ENNReal.rpow_eq_zero_iff, not_or]
  exact ⟨fun h => hx h.1, fun h => absurd hα (not_le.mpr h.2)⟩

theorem weight_rpow_ne_top {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hle : x ≤ 1) :
    x ^ α ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (ENNReal.one_rpow α ▸ ENNReal.rpow_le_rpow hle hα)

/-- The pragmatic speaker (eqs. 2/6–7): the best response to a listener kernel, with power
weights `L u {w} ^ α` scaled by the cost factor of each utterance. -/
noncomputable def speaker (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W) : Kernel W U :=
  Kernel.ofWeights fun w u => L u {w} ^ α * cost u

@[simp] theorem speaker_apply_singleton (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W) (w : W)
    (u : U) :
    speaker α cost L w {u} = L u {w} ^ α * cost u / ∑ u', L u' {w} ^ α * cost u' :=
  Kernel.ofWeights_apply_singleton _ w u

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
    (fun w => (h0 w).imp fun u hu => mul_ne_zero (weight_rpow_ne_zero hα hu) (hc0 u))
    fun w u => ENNReal.mul_ne_top (weight_rpow_ne_top hα (hle u w)) (hctop u)

/-- A literally false utterance is never produced (positive rationality). -/
theorem speaker_apply_singleton_eq_zero {α : ℝ} (hα : 0 < α) {cost : U → ℝ≥0∞}
    {L : Kernel U W} {w : W} {u : U} (h : L u {w} = 0) : speaker α cost L w {u} = 0 := by
  rw [speaker_apply_singleton, h, ENNReal.zero_rpow_of_pos hα, zero_mul, ENNReal.zero_div]

/-- A literally true utterance is produced with positive mass. -/
theorem speaker_apply_singleton_ne_zero {α : ℝ} (hα : 0 ≤ α) {cost : U → ℝ≥0∞}
    (hc0 : ∀ u, cost u ≠ 0) (hctop : ∀ u, cost u ≠ ∞) {L : Kernel U W} {w : W}
    (hle : ∀ u', L u' {w} ≤ 1) {u : U} (h : L u {w} ≠ 0) : speaker α cost L w {u} ≠ 0 := by
  rw [speaker_apply_singleton, ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨mul_ne_zero (weight_rpow_ne_zero hα h) (hc0 u),
    ENNReal.sum_ne_top.mpr fun u' _ =>
      ENNReal.mul_ne_top (weight_rpow_ne_top hα (hle u')) (hctop u')⟩

/-- A state with a unique applicable utterance produces it with certainty. -/
theorem speaker_apply_singleton_eq_one {α : ℝ} (hα : 0 < α) {cost : U → ℝ≥0∞} {u : U}
    (hc0 : cost u ≠ 0) (hctop : cost u ≠ ∞) {L : Kernel U W} {w : W} (h : L u {w} ≠ 0)
    (hle : L u {w} ≤ 1) (hother : ∀ u' ≠ u, L u' {w} = 0) : speaker α cost L w {u} = 1 := by
  rw [speaker_apply_singleton, Finset.sum_eq_single u
    (fun u' _ hu' => by rw [hother u' hu', ENNReal.zero_rpow_of_pos hα, zero_mul])
    (fun hu => absurd (Finset.mem_univ u) hu)]
  exact ENNReal.div_self (mul_ne_zero (weight_rpow_ne_zero hα.le h) hc0)
    (ENNReal.mul_ne_top (weight_rpow_ne_top hα.le hle) hctop)

omit [MeasurableSingletonClass U] in
/-- Speaker shares are at most one. -/
theorem speaker_real_singleton_le_one (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W) (w : W)
    (u : U) : (speaker α cost L w).real {u} ≤ 1 := by
  rw [measureReal_def, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    ((measure_mono (Set.subset_univ _)).trans (Kernel.ofWeights_apply_univ_le_one _ w))

/-! #### Pragmatic listeners -/

section Listener

variable [StandardBorelSpace W] [Nonempty W] (α : ℝ) (cost : U → ℝ≥0∞) (L : Kernel U W)
  (μ : Measure W) [IsFiniteMeasure μ]

/-- The pragmatic listener (eq. 3): the Bayesian inverse of the speaker against the prior. -/
noncomputable def pragmaticListener : Kernel U W := (speaker α cost L)†μ

variable [DiscreteMeasurableSpace U] [StandardBorelSpace U] [Nonempty U] [DecidableEq O]
  (obs : U → O)

omit [Countable W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U]
  [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace U] [Nonempty U] [DecidableEq O] in
theorem measurable_obs_snd : Measurable fun p : W × U => obs p.2 :=
  Measurable.of_discrete.comp measurable_snd

/-- The joint pragmatic listener (eqs. 18b/21b): when the listener hears only the form
`obs u` of the speaker's choice, the posterior over (state, choice) is the Bayesian inverse of
the deterministic observation kernel against the joint of prior and speaker. Its `fst` is
the state listener, its `snd` the choice posterior. -/
noncomputable def jointListener : Kernel O (W × U) :=
  (Kernel.deterministic (fun p : W × U => obs p.2) (measurable_obs_snd obs))†(μ ⊗ₘ speaker α cost L)

omit [MeasurableSingletonClass U] [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace U]
  [Nonempty U] [DecidableEq O] [IsFiniteMeasure μ] in
/-- The heard form is distributed as the production marginal. -/
theorem deterministic_comp_compProd_speaker :
    Kernel.deterministic (fun p : W × U => obs p.2) (measurable_obs_snd obs)
        ∘ₘ (μ ⊗ₘ speaker α cost L)
      = (speaker α cost L ∘ₘ μ).map obs := by
  rw [Measure.deterministic_comp_eq_map, show (fun p : W × U => obs p.2) = obs ∘ Prod.snd from rfl,
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

/-- State-listener preference on reals: the observation's marginal cancels, leaving
prior-weighted speaker mass pooled over the observation's fibre. -/
theorem jointListener_fst_real_lt_iff [Fintype W] {o : O}
    (ho : ((speaker α cost L ∘ₘ μ).map obs) {o} ≠ 0) (w₁ w₂ : W) :
    (jointListener α cost L μ obs o).fst.real {w₁}
        < (jointListener α cost L μ obs o).fst.real {w₂}
      ↔ (∑ u ∈ Finset.univ.filter (obs · = o), μ.real {w₁} * (speaker α cost L w₁).real {u})
        < ∑ u ∈ Finset.univ.filter (obs · = o), μ.real {w₂} * (speaker α cost L w₂).real {u} := by
  have key : ∀ w : W, (jointListener α cost L μ obs o).fst {w}
      = (∑ u ∈ Finset.univ.filter (obs · = o), μ {w} * speaker α cost L w {u})
        / ((speaker α cost L ∘ₘ μ).map obs) {o} := fun w => by
    rw [Measure.fst_apply_singleton]
    simp_rw [jointListener_apply_singleton α cost L μ obs ho, div_eq_mul_inv, ← Finset.sum_mul,
      ← Finset.sum_filter]
  have hne : ∀ w : W,
      (∑ u ∈ Finset.univ.filter (obs · = o), μ {w} * speaker α cost L w {u}) ≠ ∞ :=
    fun w => ENNReal.sum_ne_top.mpr fun u _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, key, key,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne w₁) ho) (ENNReal.div_ne_top (hne w₂) ho),
    ENNReal.div_lt_div_iff_left ho (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne w₁) (hne w₂),
    ENNReal.toReal_sum (fun u _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun u _ =>
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
    fun u hu => by
      rw [Measure.snd_apply_singleton]
      simp_rw [jointListener_apply_singleton α cost L μ obs ho, if_pos hu, div_eq_mul_inv,
        ← Finset.sum_mul]
  have hne : ∀ u : U, (∑ w, μ {w} * speaker α cost L w {u}) ≠ ∞ := fun u =>
    ENNReal.sum_ne_top.mpr fun w _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, key u₁ h₁, key u₂ h₂,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne u₁) ho) (ENNReal.div_ne_top (hne u₂) ho),
    ENNReal.div_lt_div_iff_left ho (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne u₁) (hne u₂),
    ENNReal.toReal_sum (fun w _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun w _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

end Listener

/-! #### State-side latent families

[franke-bergen-2020] eqs. 11–13 (lexical uncertainty): each speaker carries a fixed latent
index and best-responds within it — normalization is per index, in contrast to the
choice-side latents of `jointListener`, whose speaker normalizes across the pooled pairs.
The weight functions coincide; only the normalization differs. -/

section Family

variable {Λ : Type*} [MeasurableSpace Λ] [Countable Λ] [MeasurableSingletonClass Λ]

/-- The family speaker: the latent index rides in the state. -/
noncomputable def familySpeaker (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞) :
    Kernel (W × Λ) U :=
  Kernel.ofFunOfCountable fun p => speaker α cost (L p.2) p.1

omit [MeasurableSingletonClass U] in
@[simp] theorem familySpeaker_apply (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞)
    (p : W × Λ) : familySpeaker L α cost p = speaker α cost (L p.2) p.1 := rfl

instance (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞) :
    IsFiniteKernel (familySpeaker L α cost) :=
  ⟨⟨1, ENNReal.one_lt_top, fun p => by
    rw [familySpeaker_apply]
    exact Kernel.ofWeights_apply_univ_le_one _ p.1⟩⟩

/-- A member's positively produced utterance at a positive-prior state witnesses a positive
observation marginal for the family speaker. -/
theorem comp_familySpeaker_ne_zero {L : Λ → Kernel U W} {α : ℝ} {cost : U → ℝ≥0∞}
    {μ : Measure (W × Λ)} {w : W} {l : Λ} {u : U} (hμ : μ {(w, l)} ≠ 0)
    (hs : speaker α cost (L l) w {u} ≠ 0) : (familySpeaker L α cost ∘ₘ μ) {u} ≠ 0 :=
  comp_apply_singleton_ne_zero _ _ hμ (by rwa [familySpeaker_apply])

variable [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace Λ] [Nonempty Λ]

/-- The family listener (eqs. 12–13): the Bayesian inverse of the family speaker over the
joint (state, index) space. -/
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

/-- Event comparison for the family listener reduces to prior-weighted member speaker
sums. -/
theorem familyListener_real_lt_iff (L : Λ → Kernel U W) (α : ℝ) (cost : U → ℝ≥0∞) {u : U}
    (hu : (familySpeaker L α cost ∘ₘ μ) {u} ≠ 0) (E₁ E₂ : Finset (W × Λ)) :
    (familyListener L α cost μ u).real ↑E₁ < (familyListener L α cost μ u).real ↑E₂
      ↔ (∑ p ∈ E₁, μ.real {p} * (speaker α cost (L p.2) p.1).real {u})
        < ∑ p ∈ E₂, μ.real {p} * (speaker α cost (L p.2) p.1).real {u} := by
  rw [familyListener, posterior_real_finset_lt_iff _ _ hu]
  simp_rw [familySpeaker_apply]

/-- State-marginal preference for a latent family at equal priors: the latent pools,
leaving summed member speaker shares. -/
theorem familyListener_fst_real_lt_iff [Fintype Λ] (L : Λ → Kernel U W) {α : ℝ}
    {cost : U → ℝ≥0∞} (hμeq : ∀ p q : W × Λ, μ {p} = μ {q}) (hμ0 : ∀ p : W × Λ, μ {p} ≠ 0)
    {u : U} {w₀ : W} {l₀ : Λ} (hs : speaker α cost (L l₀) w₀ {u} ≠ 0) {w₁ w₂ : W} :
    (familyListener L α cost μ u).fst.real {w₁} < (familyListener L α cost μ u).fst.real {w₂}
      ↔ (∑ l, (speaker α cost (L l) w₁).real {u}) < ∑ l, (speaker α cost (L l) w₂).real {u} := by
  set p₀ : W × Λ := Classical.arbitrary _
  have key : ∀ w : W, (∑ l, μ.real {(w, l)} * (familySpeaker L α cost (w, l)).real {u})
      = μ.real {p₀} * ∑ l, (speaker α cost (L l) w).real {u} := fun w => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by
      rw [familySpeaker_apply, show μ.real {(w, l)} = μ.real {p₀} from by
        rw [measureReal_def, measureReal_def, hμeq (w, l) p₀]]
  rw [familyListener,
    posterior_fst_real_lt_iff _ _ (comp_familySpeaker_ne_zero (hμ0 (w₀, l₀)) hs), key, key,
    mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real {p₀} from ENNReal.toReal_pos (hμ0 p₀) (measure_ne_top _ _))]

/-- Latent-marginal preference for a latent family at equal priors: the states pool,
leaving summed member speaker shares. -/
theorem familyListener_snd_real_lt_iff [Fintype W] (L : Λ → Kernel U W) {α : ℝ}
    {cost : U → ℝ≥0∞} (hμeq : ∀ p q : W × Λ, μ {p} = μ {q}) (hμ0 : ∀ p : W × Λ, μ {p} ≠ 0)
    {u : U} {w₀ : W} {l₀ : Λ} (hs : speaker α cost (L l₀) w₀ {u} ≠ 0) {l₁ l₂ : Λ} :
    (familyListener L α cost μ u).snd.real {l₁} < (familyListener L α cost μ u).snd.real {l₂}
      ↔ (∑ w, (speaker α cost (L l₁) w).real {u}) < ∑ w, (speaker α cost (L l₂) w).real {u} := by
  set p₀ : W × Λ := Classical.arbitrary _
  have key : ∀ l : Λ, (∑ w, μ.real {(w, l)} * (familySpeaker L α cost (w, l)).real {u})
      = μ.real {p₀} * ∑ w, (speaker α cost (L l) w).real {u} := fun l => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by
      rw [familySpeaker_apply, show μ.real {(w, l)} = μ.real {p₀} from by
        rw [measureReal_def, measureReal_def, hμeq (w, l) p₀]]
  rw [familyListener,
    posterior_snd_real_lt_iff _ _ (comp_familySpeaker_ne_zero (hμ0 (w₀, l₀)) hs), key, key,
    mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real {p₀} from ENNReal.toReal_pos (hμ0 p₀) (measure_ne_top _ _))]

end Family

end Pipeline

end RSA
