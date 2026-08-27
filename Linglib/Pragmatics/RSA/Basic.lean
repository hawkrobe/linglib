import Mathlib.Probability.Kernel.Posterior
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Linglib.Pragmatics.RSA.Dominates

/-!
# The Rational Speech Act pipeline on probability kernels

The RSA model ([frank-goodman-2012]; [degen-2023] eqs. 1–4;
[franke-bergen-2020] eqs. 5–22) in mathlib's probability vocabulary. The
literal listener is the prior reweighted by a graded meaning, the speaker is
the best response in power-weight form (`ENNReal.rpow` is total, so falsity
needs no signed utilities), and the pragmatic listeners are mathlib's
posterior kernels `κ†μ` — of the speaker, or of the deterministic observation
kernel over the joint of prior and speaker when the listener hears only the
form of the speaker's choice. Rationality, cost, meaning, and prior are
arguments, so findings quantify over them.

The classical specialization — finite states, Boolean meanings, a uniform
prior, no cost — carries a decision procedure: speaker and listener masses
are ratios of inverse-power sums over the multisets of extension sizes
(`profile`), so preference facts close by `decide`, either uniformly in the
rationality (`Multiset.StrictDominates` certificates) or at a pinned natural
rationality (ℕ inequalities via `Multiset.divPowSum`).

## Main definitions

* `RSA.literalListener` — eq. 1: the prior reweighted by the meaning.
* `RSA.speaker` — eqs. 2/6–7: `ProbabilityTheory.Kernel.ofWeights` of `L ^ α · cost`.
* `RSA.pragmaticListener` — eq. 3: `(speaker α cost L)†μ`.
* `RSA.jointListener` — eqs. 18b/21b: the posterior over (state, choice) given
  the heard form; `.fst` is the state listener, `.snd` the choice posterior.
* `RSA.familySpeaker`, `RSA.familyListener` — state-side latents (eqs. 11–13):
  the latent is a speaker argument and normalization is per latent.
* `RSA.classicalListener`, `RSA.classicalSpeaker`, `RSA.classicalJointListener` —
  the classical specialization, with `RSA.profile` and `RSA.fiberProfile`.

## Main statements

* `ProbabilityTheory.posterior_apply_singleton` — exact Bayes for `κ†μ` at a
  positive-mass observation.
* `RSA.classicalJointListener_fst_real_lt_of_prodMul_strictDominates` — the
  certificate register: strict dominance of profile products decides listener
  preference uniformly in the rationality.
* `RSA.classicalJointListener_fst_real_lt_of_divPowSum`,
  `RSA.classicalJointListener_snd_real_lt_of_divPowSum` — the evaluation
  register: at a natural rationality, preference is a decided ℕ inequality.

## Implementation notes

All spaces here are finite and discrete; the ⊤ σ-algebra makes every study
enum standard Borel, so mathlib's disintegration-based conditionals apply.
Their characterization is almost-everywhere, but an ae-fact holds at every
atom of positive mass (`MeasureTheory.ae_of_singleton_ne_zero`), which
yields exact Bayes pointwise — no `rnDeriv`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Almost-everywhere facts at atoms -/

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- An almost-everywhere property holds at any atom of positive mass. -/
theorem ae_of_singleton_ne_zero {ν : Measure α} {P : α → Prop}
    (h : ∀ᵐ x ∂ν, P x) {x : α} (hx : ν {x} ≠ 0) : P x := by
  by_contra hP
  exact hx (measure_mono_null (fun y hy => (Set.mem_singleton_iff.mp hy) ▸ hP) h)

end MeasureTheory

/-! ### Kernels from weight functions -/

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [Fintype β] [MeasurableSingletonClass β] in
theorem ofFunOfCountable_apply (f : α → Measure β) (a : α) : ofFunOfCountable f a = f a := rfl

/-- The kernel that normalizes a nonnegative weight function on a finite
target: row `a` is the probability measure proportional to `w a`. A row of
zero (or infinite) total weight collapses to the zero measure. -/
noncomputable def ofWeights (w : α → β → ℝ≥0∞) : Kernel α β :=
  ofFunOfCountable fun a => (∑ b, w a b)⁻¹ • ∑ b, w a b • Measure.dirac b

@[simp] theorem ofWeights_apply_singleton (w : α → β → ℝ≥0∞) (a : α) (b : β) :
    ofWeights w a {b} = w a b / ∑ b', w a b' := by
  have hval : (∑ b', w a b' • Measure.dirac b') {b} = w a b := by
    rw [Measure.finsetSum_apply,
      Finset.sum_eq_single_of_mem b (Finset.mem_univ b) fun b' _ hb' => by
        rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (.singleton b),
          Set.indicator_of_notMem (fun h => hb' (Set.mem_singleton_iff.mp h)), mul_zero],
      Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (.singleton b),
      Set.indicator_of_mem (Set.mem_singleton b), Pi.one_apply, mul_one]
  show ((∑ b', w a b')⁻¹ • ∑ b', w a b' • Measure.dirac b') {b} = _
  rw [Measure.smul_apply, smul_eq_mul, hval, ENNReal.div_eq_inv_mul]

omit [MeasurableSingletonClass β] in
/-- A row with a positive entry and finite entries normalizes to a
probability measure. -/
theorem isMarkovKernel_ofWeights {w : α → β → ℝ≥0∞}
    (h0 : ∀ a, ∃ b, w a b ≠ 0) (htop : ∀ a b, w a b ≠ ∞) :
    IsMarkovKernel (ofWeights w) := by
  refine ⟨fun a => ⟨?_⟩⟩
  have hZ0 : (∑ b, w a b) ≠ 0 := by
    obtain ⟨b, hb⟩ := h0 a
    exact fun h => hb (Finset.sum_eq_zero_iff.mp h b (Finset.mem_univ b))
  have hZtop : (∑ b, w a b) ≠ ∞ := ENNReal.sum_ne_top.mpr fun b _ => htop a b
  show ((∑ b, w a b)⁻¹ • ∑ b, w a b • Measure.dirac b) Set.univ = 1
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel hZ0 hZtop

/-- Row-preference in a weight kernel reduces to weight comparison; the
normalization cancels. -/
theorem ofWeights_real_singleton_lt_iff {w : α → β → ℝ≥0∞} (a : α)
    (h0 : (∑ b, w a b) ≠ 0) (htop : (∑ b, w a b) ≠ ∞) {b₁ b₂ : β} :
    (ofWeights w a).real {b₁} < (ofWeights w a).real {b₂} ↔ w a b₁ < w a b₂ := by
  have hb : ∀ b, w a b ≠ ∞ := fun b => ENNReal.sum_ne_top.mp htop b (Finset.mem_univ b)
  rw [measureReal_def, measureReal_def, ofWeights_apply_singleton,
    ofWeights_apply_singleton,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hb b₁) h0)
      (ENNReal.div_ne_top (hb b₂) h0),
    ENNReal.div_lt_div_iff_left h0 htop]

omit [MeasurableSingletonClass β] in
/-- Weight-kernel rows are subprobabilities: normalization gives mass 1 on
positive finite total weight and 0 otherwise. -/
theorem ofWeights_apply_univ_le_one (w : α → β → ℝ≥0∞) (a : α) :
    ofWeights w a Set.univ ≤ 1 := by
  show ((∑ b, w a b)⁻¹ • ∑ b, w a b • Measure.dirac b) Set.univ ≤ 1
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rcases eq_or_ne (∑ b, w a b) 0 with h0 | h0
  · simp [h0]
  · rcases eq_or_ne (∑ b, w a b) ∞ with htop | htop
    · simp [htop]
    · rw [ENNReal.inv_mul_cancel h0 htop]

instance (w : α → β → ℝ≥0∞) : IsFiniteKernel (ofWeights w) :=
  ⟨⟨1, ENNReal.one_lt_top, ofWeights_apply_univ_le_one w⟩⟩

end ProbabilityTheory.Kernel

/-! ### Exact Bayes for the posterior kernel at atoms -/

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]
  [MeasurableSingletonClass Ω] [MeasurableSingletonClass 𝓧]
  [StandardBorelSpace Ω] [Nonempty Ω]
  (κ : Kernel Ω 𝓧) (μ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteKernel κ]

/-- Exact Bayes for the posterior kernel at a positive-mass observation:
evaluate the defining compProd identity on a singleton rectangle. -/
theorem posterior_apply_singleton {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (ω : Ω) :
    (κ†μ) x {ω} = μ {ω} * κ ω {x} / (κ ∘ₘ μ) {x} := by
  have hrect := congrArg (fun m => m ({x} ×ˢ {ω}))
    (compProd_posterior_eq_map_swap (κ := κ) (μ := μ))
  beta_reduce at hrect
  rw [Measure.compProd_apply_prod (.singleton x) (.singleton ω),
    Measure.map_apply measurable_swap ((MeasurableSet.singleton x).prod (.singleton ω)),
    Set.preimage_swap_prod,
    Measure.compProd_apply_prod (.singleton ω) (.singleton x),
    lintegral_singleton, lintegral_singleton] at hrect
  rw [ENNReal.eq_div_iff hx (measure_ne_top _ _), mul_comm]
  rw [hrect]
  ring

/-- A single state of positive prior mass and positive emission witnesses a
positive observation marginal. -/
theorem comp_apply_singleton_ne_zero {Ω' 𝓧' : Type*} [MeasurableSpace Ω']
    [MeasurableSpace 𝓧'] [MeasurableSingletonClass 𝓧'] (κ : Kernel Ω' 𝓧')
    (μ : Measure Ω') {w : Ω'} {x : 𝓧'} (hμ : μ {w} ≠ 0) (hκ : κ w {x} ≠ 0) :
    (κ ∘ₘ μ) {x} ≠ 0 := by
  rw [Measure.bind_apply (.singleton x) (Kernel.aemeasurable _),
    ← pos_iff_ne_zero, lintegral_pos_iff_support (Kernel.measurable_coe _ (.singleton x))]
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hμ)
    (measure_mono (Set.singleton_subset_iff.mpr hκ))

end ProbabilityTheory

/-! ### Marginal evaluation on finite products -/

namespace MeasureTheory.Measure

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
  [MeasurableSingletonClass Ω] [MeasurableSingletonClass Θ]

theorem fst_apply_singleton [Fintype Θ] (m : Measure (Ω × Θ)) (ω : Ω) :
    m.fst {ω} = ∑ θ : Θ, m {(ω, θ)} := by
  rw [Measure.fst_apply (.singleton ω),
    show Prod.fst ⁻¹' ({ω} : Set Ω) = ↑(({ω} : Finset Ω) ×ˢ (Finset.univ : Finset Θ)) from by
      ext ⟨a, θ⟩; simp [eq_comm],
    ← sum_measure_singleton, Finset.sum_product, Finset.sum_singleton]

theorem snd_apply_singleton [Fintype Ω] (m : Measure (Ω × Θ)) (θ : Θ) :
    m.snd {θ} = ∑ ω : Ω, m {(ω, θ)} := by
  rw [Measure.snd_apply (.singleton θ),
    show Prod.snd ⁻¹' ({θ} : Set Θ) = ↑((Finset.univ : Finset Ω) ×ˢ ({θ} : Finset Θ)) from by
      ext ⟨a, b⟩; simp [eq_comm],
    ← sum_measure_singleton, Finset.sum_product]
  exact Finset.sum_congr rfl fun ω _ => Finset.sum_singleton _ _

end MeasureTheory.Measure

/-! ### Uniform priors on reals -/

namespace MeasureTheory

variable {W : Type*} [MeasurableSpace W] [MeasurableSingletonClass W] [Fintype W]

theorem uniformOn_univ_real_singleton (w : W) :
    (uniformOn (Set.univ : Set W)).real {w} = (Fintype.card W : ℝ)⁻¹ := by
  rw [measureReal_def, uniformOn_univ, Measure.count_singleton, one_div,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem uniformOn_univ_real_coe_finset (s : Finset W) :
    (uniformOn (Set.univ : Set W)).real ↑s = s.card / Fintype.card W := by
  rw [measureReal_def, uniformOn_univ, Measure.count_apply_finset, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]

end MeasureTheory

/-! ### Marginal listener preference over product parameter spaces -/

namespace ProbabilityTheory

variable {𝓧 : Type*} [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧]

/-- Marginal listener preference over a product parameter space, on reals:
for latent-in-the-state models, the observation's marginal cancels and the
latent pools. -/
theorem posterior_fst_real_lt_iff {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [Fintype B]
    [StandardBorelSpace A] [Nonempty A] [StandardBorelSpace B] [Nonempty B]
    (κ : Kernel (A × B) 𝓧) (μ : Measure (A × B)) [IsFiniteMeasure μ] [IsFiniteKernel κ]
    {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (a₁ a₂ : A) :
    ((κ†μ) x).fst.real {a₁} < ((κ†μ) x).fst.real {a₂}
      ↔ (∑ b, μ.real {(a₁, b)} * (κ (a₁, b)).real {x})
          < ∑ b, μ.real {(a₂, b)} * (κ (a₂, b)).real {x} := by
  have hne : ∀ a : A, (∑ b, μ {(a, b)} * κ (a, b) {x}) ≠ ∞ := fun a =>
    ENNReal.sum_ne_top.mpr fun b _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, Measure.fst_apply_singleton,
    Measure.fst_apply_singleton]
  simp_rw [posterior_apply_singleton κ μ hx, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne a₁) hx)
      (ENNReal.div_ne_top (hne a₂) hx),
    ENNReal.div_lt_div_iff_left hx (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne a₁) (hne a₂),
    ENNReal.toReal_sum (fun b _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun b _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

/-- Marginal listener preference over the latent component of a product
parameter space, on reals: the states pool. -/
theorem posterior_snd_real_lt_iff {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [Fintype A]
    [StandardBorelSpace A] [Nonempty A] [StandardBorelSpace B] [Nonempty B]
    (κ : Kernel (A × B) 𝓧) (μ : Measure (A × B)) [IsFiniteMeasure μ] [IsFiniteKernel κ]
    {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (b₁ b₂ : B) :
    ((κ†μ) x).snd.real {b₁} < ((κ†μ) x).snd.real {b₂}
      ↔ (∑ a, μ.real {(a, b₁)} * (κ (a, b₁)).real {x})
          < ∑ a, μ.real {(a, b₂)} * (κ (a, b₂)).real {x} := by
  have hne : ∀ b : B, (∑ a, μ {(a, b)} * κ (a, b) {x}) ≠ ∞ := fun b =>
    ENNReal.sum_ne_top.mpr fun a _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, Measure.snd_apply_singleton,
    Measure.snd_apply_singleton]
  simp_rw [posterior_apply_singleton κ μ hx, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne b₁) hx)
      (ENNReal.div_ne_top (hne b₂) hx),
    ENNReal.div_lt_div_iff_left hx (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne b₁) (hne b₂),
    ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

end ProbabilityTheory

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

end LiteralListener

variable [Countable W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U]

private theorem weight_rpow_ne_zero {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hx : x ≠ 0) :
    x ^ α ≠ 0 := by
  rw [ne_eq, ENNReal.rpow_eq_zero_iff, not_or]
  exact ⟨fun h => hx h.1, fun h => absurd hα (not_le.mpr h.2)⟩

private theorem weight_rpow_ne_top {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hle : x ≤ 1) :
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

/-! ### The classical specialization

Finite states, Boolean meanings, a uniform prior, and no cost: the model of
[franke-bergen-2020] eqs. 5–9 and the setting of its informativity profiles. Every
definition here is the general pipeline at these arguments; the lemmas reduce the kernels to
the combinatorics of extension sizes. -/

section Classical

variable {T C O : Type*} [Fintype T] [DecidableEq T] [MeasurableSpace T]
  [DiscreteMeasurableSpace T] [Fintype C] [MeasurableSpace C] [DiscreteMeasurableSpace C]
  (sem : C → Finset T)

/-- The classical literal listener (eq. 5): uniform on each choice's extension. -/
noncomputable def classicalListener : Kernel C T :=
  literalListener (uniformOn Set.univ) fun c => (↑(sem c) : Set T).indicator 1

omit [DecidableEq T] in
theorem classicalListener_apply (c : C) : classicalListener sem c = uniformOn ↑(sem c) := by
  rw [classicalListener, literalListener_indicator, Kernel.ofFunOfCountable_apply]
  rw [uniformOn, uniformOn, cond_cond_eq_cond_inter' MeasurableSet.univ .of_discrete
    (by rw [Measure.count_apply_finite _ Set.finite_univ]; exact ENNReal.natCast_ne_top _),
    Set.univ_inter]

theorem classicalListener_apply_singleton (c : C) (t : T) :
    classicalListener sem c {t} = if t ∈ sem c then ((sem c).card : ℝ≥0∞)⁻¹ else 0 := by
  rw [classicalListener_apply, uniformOn, cond_apply (sem c).measurableSet,
    Measure.count_apply_finset]
  split
  · rw [show ↑(sem c) ∩ {t} = ({t} : Set T) from
        Set.inter_eq_self_of_subset_right (by simpa using ‹t ∈ sem c›),
      Measure.count_singleton, mul_one]
  · rw [show ↑(sem c) ∩ {t} = (∅ : Set T) from by
        simpa [Set.eq_empty_iff_forall_notMem] using ‹t ∉ sem c›,
      measure_empty, mul_zero]

theorem classicalListener_apply_singleton_le_one (c : C) (t : T) :
    classicalListener sem c {t} ≤ 1 := by
  rw [classicalListener_apply_singleton]
  split
  · exact ENNReal.inv_le_one.mpr (by exact_mod_cast Finset.card_pos.mpr ⟨t, ‹_›⟩)
  · exact zero_le_one

theorem classicalListener_apply_singleton_ne_zero {c : C} {t : T} (h : t ∈ sem c) :
    classicalListener sem c {t} ≠ 0 := by
  rw [classicalListener_apply_singleton, if_pos h]
  simp

/-- The classical speaker (eq. 7): best response to `classicalListener` at no cost. -/
noncomputable abbrev classicalSpeaker (α : ℝ) : Kernel T C := speaker α 1 (classicalListener sem)

omit [DecidableEq T] in
theorem classicalSpeaker_apply_singleton (α : ℝ) (t : T) (c : C) :
    classicalSpeaker sem α t {c}
      = classicalListener sem c {t} ^ α / ∑ c', classicalListener sem c' {t} ^ α := by
  simp only [classicalSpeaker, speaker_apply_singleton, Pi.one_apply, mul_one]

omit [DecidableEq T] in
theorem classicalSpeaker_apply_univ_le_one (α : ℝ) (t : T) :
    classicalSpeaker sem α t Set.univ ≤ 1 :=
  Kernel.ofWeights_apply_univ_le_one _ t

/-- Every state has a true choice — the proviso making the classical speaker a probability
kernel. -/
theorem isMarkovKernel_classicalSpeaker {α : ℝ} (hα : 0 ≤ α) (hsem : ∀ t, ∃ c, t ∈ sem c) :
    IsMarkovKernel (classicalSpeaker sem α) :=
  isMarkovKernel_speaker hα (fun _ => one_ne_zero) (fun _ => ENNReal.one_ne_top) _
    (fun c t => classicalListener_apply_singleton_le_one sem c t)
    fun t => (hsem t).imp fun _ h => classicalListener_apply_singleton_ne_zero sem h

theorem classicalSpeaker_apply_singleton_eq_zero {α : ℝ} (hα : 0 < α) {t : T} {c : C}
    (h : t ∉ sem c) : classicalSpeaker sem α t {c} = 0 :=
  speaker_apply_singleton_eq_zero hα (by rw [classicalListener_apply_singleton, if_neg h])

theorem classicalSpeaker_apply_singleton_ne_zero {α : ℝ} (hα : 0 ≤ α) {t : T} {c : C}
    (h : t ∈ sem c) : classicalSpeaker sem α t {c} ≠ 0 :=
  speaker_apply_singleton_ne_zero hα (fun _ => one_ne_zero) (fun _ => ENNReal.one_ne_top)
    (fun c' => classicalListener_apply_singleton_le_one sem c' t)
    (classicalListener_apply_singleton_ne_zero sem h)

/-! #### Informativity profiles

The combinatorial shadow of the model: the multiset of extension sizes of a state's true
choices. Softmax masses are ratios of `Multiset.invPowSum`s over profiles, so preference
certificates are `Multiset.StrictDominates` facts closed by `decide` — uniform in the
rationality. -/

variable [DecidableEq O] (obs : C → O)

/-- The choices true at a state. -/
def trueChoices (t : T) : Finset C := Finset.univ.filter (t ∈ sem ·)

/-- The informativity profile: extension sizes of the true choices. -/
def profile (t : T) : Multiset ℕ := (trueChoices sem t).val.map fun c => (sem c).card

/-- The profile restricted to choices heard as `o`. -/
def fiberProfile (o : O) (t : T) : Multiset ℕ :=
  ((trueChoices sem t).filter (obs · = o)).val.map fun c => (sem c).card

/-- The profile of true choices heard otherwise. -/
def restProfile (o : O) (t : T) : Multiset ℕ :=
  ((trueChoices sem t).filter (obs · ≠ o)).val.map fun c => (sem c).card

omit [Fintype T] [MeasurableSpace T] [DiscreteMeasurableSpace T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] in
theorem profile_eq_fiberProfile_add_restProfile (o : O) (t : T) :
    profile sem t = fiberProfile sem obs o t + restProfile sem obs o t := by
  rw [fiberProfile, restProfile, ← Multiset.map_add, profile]
  congr 1
  rw [Finset.filter_val, Finset.filter_val, Multiset.filter_add_not]

omit [Fintype T] [MeasurableSpace T] [DiscreteMeasurableSpace T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] [DecidableEq O] in
theorem zero_notMem_profile (t : T) : 0 ∉ profile sem t := by
  simp only [profile, Multiset.mem_map, not_exists, not_and]
  intro c hc hcard
  rw [Finset.mem_val, trueChoices, Finset.mem_filter] at hc
  exact Finset.card_ne_zero_of_mem hc.2 hcard

omit [Fintype T] [MeasurableSpace T] [DiscreteMeasurableSpace T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] in
theorem zero_notMem_fiberProfile (o : O) (t : T) : 0 ∉ fiberProfile sem obs o t := fun h =>
  zero_notMem_profile sem t
    (profile_eq_fiberProfile_add_restProfile sem obs o t ▸ Multiset.mem_add.mpr (Or.inl h))

omit [Fintype T] [MeasurableSpace T] [DiscreteMeasurableSpace T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] in
theorem zero_notMem_restProfile (o : O) (t : T) : 0 ∉ restProfile sem obs o t := fun h =>
  zero_notMem_profile sem t
    (profile_eq_fiberProfile_add_restProfile sem obs o t ▸ Multiset.mem_add.mpr (Or.inr h))

omit [Fintype T] [MeasurableSpace T] [DiscreteMeasurableSpace T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] in
/-- A nonempty fibre profile exhibits an `o`-shaped true choice — certificates carry their
own truth witnesses. -/
theorem exists_of_fiberProfile_ne_zero {o : O} {t : T} (h : fiberProfile sem obs o t ≠ 0) :
    ∃ c, obs c = o ∧ t ∈ sem c := by
  rw [fiberProfile, ne_eq, Multiset.map_eq_zero, Finset.val_eq_zero, ← ne_eq,
    ← Finset.nonempty_iff_ne_empty] at h
  obtain ⟨c, hc⟩ := h
  rw [Finset.mem_filter, trueChoices, Finset.mem_filter] at hc
  exact ⟨c, hc.2, hc.1.2⟩

omit [Fintype T] [MeasurableSpace T] [DiscreteMeasurableSpace T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] [DecidableEq O] in
theorem profile_ne_zero (hsem : ∀ t, ∃ c, t ∈ sem c) (t : T) : profile sem t ≠ 0 := by
  obtain ⟨c, hc⟩ := hsem t
  intro h
  rw [profile, Multiset.map_eq_zero, Finset.val_eq_zero] at h
  exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩) (h ▸ Finset.notMem_empty c)

omit [DecidableEq O] in
theorem sum_rpow_classicalListener {α : ℝ} (hα : 0 < α) (t : T) :
    ∑ c, classicalListener sem c {t} ^ α = (profile sem t).invPowSum α := by
  simp_rw [classicalListener_apply_singleton, apply_ite (· ^ α), ENNReal.zero_rpow_of_pos hα,
    ← Finset.sum_filter]
  rw [profile, Multiset.invPowSum, Multiset.map_map]
  rfl

theorem sum_fiber_rpow_classicalListener {α : ℝ} (hα : 0 < α) (o : O) (t : T) :
    ∑ c ∈ Finset.univ.filter (obs · = o), classicalListener sem c {t} ^ α
      = (fiberProfile sem obs o t).invPowSum α := by
  simp_rw [classicalListener_apply_singleton, apply_ite (· ^ α), ENNReal.zero_rpow_of_pos hα,
    ← Finset.sum_filter]
  rw [fiberProfile, Multiset.invPowSum, Multiset.map_map,
    show (Finset.univ.filter (obs · = o)).filter (fun c => t ∈ sem c)
      = (trueChoices sem t).filter (obs · = o) from by
    rw [trueChoices, Finset.filter_comm]]
  rfl

/-- Pooled speaker mass over an observation's fibre is a ratio of profile sums —
[franke-bergen-2020] eq. 8, structurally. -/
theorem sum_fiber_classicalSpeaker {α : ℝ} (hα : 0 < α) (o : O) (t : T) :
    ∑ c ∈ Finset.univ.filter (obs · = o), classicalSpeaker sem α t {c}
      = (fiberProfile sem obs o t).invPowSum α / (profile sem t).invPowSum α := by
  simp_rw [classicalSpeaker_apply_singleton, div_eq_mul_inv, ← Finset.sum_mul]
  rw [sum_fiber_rpow_classicalListener sem obs hα, sum_rpow_classicalListener sem hα,
    ← div_eq_mul_inv]

omit [DecidableEq O] in
/-- Exact speaker mass on reals: extension-size weight over the state's partition. -/
theorem classicalSpeaker_real_singleton {α : ℝ} (hα : 0 < α) (t : T) (c : C) :
    (classicalSpeaker sem α t).real {c}
      = (if t ∈ sem c then (((sem c).card : ℝ))⁻¹ ^ α else 0)
        / ((profile sem t).invPowSum α).toReal := by
  rw [measureReal_def, classicalSpeaker_apply_singleton, sum_rpow_classicalListener sem hα,
    ENNReal.toReal_div, classicalListener_apply_singleton, apply_ite (· ^ α),
    ENNReal.zero_rpow_of_pos hα, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast]

omit [DecidableEq O] in
theorem classicalSpeaker_real_singleton_eq_zero {α : ℝ} (hα : 0 < α) {t : T} {c : C}
    (h : t ∉ sem c) : (classicalSpeaker sem α t).real {c} = 0 := by
  rw [measureReal_def, classicalSpeaker_apply_singleton_eq_zero sem hα h, ENNReal.toReal_zero]

omit [DecidableEq T] [DecidableEq O] in
/-- Speaker shares over any set of choices stay within the row's unit mass. -/
theorem sum_classicalSpeaker_real_singleton_le_one (α : ℝ) (t : T) (S : Finset C) :
    ∑ c ∈ S, (classicalSpeaker sem α t).real {c} ≤ 1 := by
  have hle : classicalSpeaker sem α t ↑S ≤ 1 :=
    le_trans (measure_mono (Set.subset_univ _)) (classicalSpeaker_apply_univ_le_one sem α t)
  calc ∑ c ∈ S, (classicalSpeaker sem α t).real {c}
      = (classicalSpeaker sem α t).real ↑S := by
        simp_rw [measureReal_def, ← ENNReal.toReal_sum fun c _ => measure_ne_top _ _,
          sum_measure_singleton]
    _ ≤ 1 := by
        rw [measureReal_def, ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono ENNReal.one_ne_top hle

omit [DecidableEq O] in
/-- Competition: any other true choice caps a share strictly below one. -/
theorem classicalSpeaker_real_singleton_lt_one [DecidableEq C] {α : ℝ} (hα : 0 ≤ α) {t : T}
    {c c' : C} (hne : c' ≠ c) (hmem' : t ∈ sem c') : (classicalSpeaker sem α t).real {c} < 1 := by
  have hsum := sum_classicalSpeaker_real_singleton_le_one sem α t {c, c'}
  rw [Finset.sum_insert (by simpa using fun h => hne h.symm), Finset.sum_singleton] at hsum
  have hpos : 0 < (classicalSpeaker sem α t).real {c'} :=
    ENNReal.toReal_pos (classicalSpeaker_apply_singleton_ne_zero sem hα hmem')
      (measure_ne_top _ _)
  linarith

omit [DecidableEq O] in
/-- Informativity monotonicity ([franke-bergen-2020] eq. 7's qualitative claim): between two
true choices, the one with the strictly smaller extension is produced with strictly higher
probability, at every positive rationality. -/
theorem classicalSpeaker_real_singleton_lt_of_card_lt {α : ℝ} (hα : 0 < α) {t : T} {c c' : C}
    (hmem : t ∈ sem c) (hmem' : t ∈ sem c') (hcard : (sem c').card < (sem c).card) :
    (classicalSpeaker sem α t).real {c} < (classicalSpeaker sem α t).real {c'} := by
  have hterm : classicalListener sem c {t} ^ α * (1 : C → ℝ≥0∞) c ≠ 0 :=
    mul_ne_zero (weight_rpow_ne_zero hα.le (classicalListener_apply_singleton_ne_zero sem hmem))
      one_ne_zero
  have hZ0 : (∑ u, classicalListener sem u {t} ^ α * (1 : C → ℝ≥0∞) u) ≠ 0 := fun h =>
    hterm (le_antisymm (le_trans
      (Finset.single_le_sum (f := fun u => classicalListener sem u {t} ^ α * (1 : C → ℝ≥0∞) u)
        (fun u _ => zero_le) (Finset.mem_univ c)) h.le) zero_le)
  rw [classicalSpeaker, speaker, Kernel.ofWeights_real_singleton_lt_iff t hZ0
      (ENNReal.sum_ne_top.mpr fun u _ => ENNReal.mul_ne_top
        (weight_rpow_ne_top hα.le (classicalListener_apply_singleton_le_one sem u t))
        ENNReal.one_ne_top),
    classicalListener_apply_singleton, classicalListener_apply_singleton, if_pos hmem,
    if_pos hmem']
  simp only [Pi.one_apply, mul_one]
  exact ENNReal.rpow_lt_rpow (ENNReal.inv_lt_inv.2 (by exact_mod_cast hcard)) hα

omit [DecidableEq O] in
/-- Softmax constant-utility invariance: when every true choice at a state has the same
extension size, the speaker is uniform on them — each share is `m⁻¹` regardless of the
rationality. -/
theorem classicalSpeaker_real_singleton_of_profile_replicate {α : ℝ} (hα : 0 < α) {t : T}
    {c : C} {m n : ℕ} (hprof : profile sem t = Multiset.replicate m n) (hmem : t ∈ sem c) :
    (classicalSpeaker sem α t).real {c} = (m : ℝ)⁻¹ := by
  have hcmem : (sem c).card ∈ profile sem t :=
    Multiset.mem_map_of_mem _ (by
      rw [Finset.mem_val, trueChoices, Finset.mem_filter]
      exact ⟨Finset.mem_univ c, hmem⟩)
  have hn : (sem c).card = n := Multiset.eq_of_mem_replicate (hprof ▸ hcmem)
  have hn0 : n ≠ 0 := hn ▸ Finset.card_ne_zero_of_mem hmem
  have hx : (0 : ℝ) < ((n : ℝ))⁻¹ ^ α := Real.rpow_pos_of_pos (by positivity) α
  rw [classicalSpeaker_real_singleton sem hα, if_pos hmem, hprof, hn,
    show ((Multiset.replicate m n).invPowSum α).toReal = m * ((n : ℝ))⁻¹ ^ α by
      rw [Multiset.invPowSum_replicate, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast],
    div_mul_eq_div_div_swap, div_self hx.ne', one_div]

/-- The ℕ-cleared production mass of a choice, pooled over its true states: its
common-denominator weight times, per true state, the product of the other states' cleared
partition sums. Pooled evaluation-register hypotheses compare these. -/
def pooledDivPowSum (D k : ℕ) (c : C) : ℕ :=
  (D / (sem c).card) ^ k
    * ∑ t ∈ sem c, ∏ t' ∈ Finset.univ.erase t, (profile sem t').divPowSum D k

omit [MeasurableSpace T] [DiscreteMeasurableSpace T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] [DecidableEq O] in
private theorem pooledDivPowSum_eq (D k : ℕ) (c : C) :
    pooledDivPowSum sem D k c
      = ∑ t : T, if t ∈ sem c then
          (D / (sem c).card) ^ k * ∏ t' ∈ Finset.univ.erase t, (profile sem t').divPowSum D k
        else 0 := by
  rw [pooledDivPowSum, Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]

omit [DecidableEq O] in
/-- Exact speaker mass at a natural rationality, as a ratio of ℕ-valued common-denominator
sums. -/
theorem classicalSpeaker_real_singleton_divPowSum {k D : ℕ} [NeZero k] [NeZero D] {t : T}
    (hdvd : ∀ n ∈ profile sem t, n ∣ D) (c : C) :
    (classicalSpeaker sem k t).real {c}
      = (if t ∈ sem c then (((D / (sem c).card) ^ k : ℕ) : ℝ) else 0)
        / ((profile sem t).divPowSum D k : ℝ) := by
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hDk : ((D : ℝ) ^ k) ≠ 0 := pow_ne_zero k (Nat.cast_ne_zero.mpr (NeZero.ne D))
  rw [classicalSpeaker_real_singleton sem hα, Multiset.invPowSum_toReal_eq (NeZero.ne D) k hdvd]
  split
  · have hcard : (sem c).card ∣ D := hdvd _ (Multiset.mem_map_of_mem _ (by
      rw [Finset.mem_val, trueChoices, Finset.mem_filter]
      exact ⟨Finset.mem_univ c, ‹_›⟩))
    have hcard0 : ((sem c).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      fun h0 => NeZero.ne D (Nat.eq_zero_of_zero_dvd (h0 ▸ hcard))
    have hinv : (((sem c).card : ℝ))⁻¹ = ((D / (sem c).card : ℕ) : ℝ) / D := by
      rw [eq_div_iff (Nat.cast_ne_zero.mpr (NeZero.ne D)),
        show (D : ℝ) = ((D / (sem c).card : ℕ) : ℝ) * ((sem c).card : ℝ) by
          rw [← Nat.cast_mul, Nat.div_mul_cancel hcard],
        mul_comm _ ((sem c).card : ℝ), ← mul_assoc, inv_mul_cancel₀ hcard0, one_mul]
    rw [Real.rpow_natCast, hinv, div_pow, ← Nat.cast_pow, ← Nat.cast_pow, div_div_div_comm,
      div_self (Nat.cast_ne_zero.mpr (pow_ne_zero k (NeZero.ne D)) : ((D ^ k : ℕ) : ℝ) ≠ 0),
      div_one]
  · rw [zero_div, zero_div]

/-! #### The classical listener -/

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty T] [Nonempty C]

/-- The classical joint listener (eqs. 18b/21b): the pragmatic listener of the classical
speaker at a uniform prior, hearing the form of the speaker's choice. -/
noncomputable abbrev classicalJointListener (α : ℝ) : Kernel O (T × C) :=
  jointListener α 1 (classicalListener sem) (uniformOn Set.univ) obs

omit [DecidableEq O] [Nonempty T] [Nonempty C] in
/-- A state truly described by an `o`-shaped choice witnesses a positive observation
marginal. -/
theorem map_comp_classicalSpeaker_ne_zero {α : ℝ} (hα : 0 ≤ α) {t : T} {c : C} {o : O}
    (hc : obs c = o) (hmem : t ∈ sem c) :
    ((classicalSpeaker sem α ∘ₘ uniformOn Set.univ).map obs) {o} ≠ 0 :=
  map_comp_speaker_ne_zero α 1 (classicalListener sem) _ obs
    (by rw [uniformOn_univ, Measure.count_singleton]; simp) hc
    (classicalSpeaker_apply_singleton_ne_zero sem hα hmem)

omit [DecidableEq T] [Nonempty T] in
private theorem uniformOn_univ_real_singleton_eq (t t' : T) :
    (uniformOn (Set.univ : Set T)).real {t} = (uniformOn Set.univ).real {t'} := by
  rw [uniformOn_univ_real_singleton, uniformOn_univ_real_singleton]

private theorem sum_div_lt_sum_div_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {a b z : ι → ℝ}
    (hz : ∀ i, 0 < z i) :
    (∑ i, a i / z i) < (∑ i, b i / z i)
      ↔ (∑ i, a i * ∏ j ∈ Finset.univ.erase i, z j)
          < ∑ i, b i * ∏ j ∈ Finset.univ.erase i, z j := by
  have hP : (0 : ℝ) < ∏ j, z j := Finset.prod_pos fun j _ => hz j
  have key : ∀ f : ι → ℝ, (∑ i, f i / z i) * ∏ j, z j
      = ∑ i, f i * ∏ j ∈ Finset.univ.erase i, z j := by
    intro f
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_mul_eq_mul_div, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), ← mul_assoc,
      mul_div_assoc, div_self (hz i).ne', mul_one]
  rw [← mul_lt_mul_iff_left₀ hP, key, key]

/-- The evaluation register for the choice posterior at a natural rationality: pooled
preference between two `o`-shaped choices is the ℕ-valued common-denominator comparison over
all states — a kernel `decide`. The strict inequality carries its own truth witness. -/
theorem classicalJointListener_snd_real_lt_of_divPowSum (hsem : ∀ t, ∃ c, t ∈ sem c) {k D : ℕ}
    [NeZero k] [NeZero D] (hdvd : ∀ t : T, ∀ n ∈ profile sem t, n ∣ D) {o : O} {c₁ c₂ : C}
    (h₁ : obs c₁ = o) (h₂ : obs c₂ = o)
    (hlt : pooledDivPowSum sem D k c₁ < pooledDivPowSum sem D k c₂) :
    (classicalJointListener sem obs k o).snd.real {c₁}
      < (classicalJointListener sem obs k o).snd.real {c₂} := by
  rw [pooledDivPowSum_eq, pooledDivPowSum_eq] at hlt
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) hlt))
  have hmem₀ : t₀ ∈ sem c₂ := by
    by_contra h
    exact ht₀ (if_neg h)
  have hprior : ∀ c : C,
      (∑ t : T, (uniformOn (Set.univ : Set T)).real {t} * (classicalSpeaker sem k t).real {c})
      = (uniformOn (Set.univ : Set T)).real {t₀} * ∑ t : T,
          (if t ∈ sem c then (((D / (sem c).card) ^ k : ℕ) : ℝ) else 0)
            / ((profile sem t).divPowSum D k : ℝ) := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [uniformOn_univ_real_singleton_eq t t₀,
      classicalSpeaker_real_singleton_divPowSum sem (hdvd t)]
  rw [classicalJointListener, jointListener_snd_real_lt_iff _ _ _ _ _
      (map_comp_classicalSpeaker_ne_zero sem obs hα.le h₂ hmem₀) h₁ h₂, hprior, hprior,
    mul_lt_mul_iff_right₀ (show (0 : ℝ) < (uniformOn (Set.univ : Set T)).real {t₀} from
      ENNReal.toReal_pos (by rw [uniformOn_univ, Measure.count_singleton]; simp)
        (measure_ne_top _ _)),
    sum_div_lt_sum_div_iff fun t => by
      exact_mod_cast Multiset.divPowSum_pos (NeZero.ne D) (hdvd t) (profile_ne_zero sem hsem t)]
  simp only [ite_mul, zero_mul]
  exact_mod_cast hlt

/-- Listener preference reduces to the cross-multiplied profile comparison, on reals: the
observation marginal and the shared prior cancel. Both registers' closers enter here. -/
theorem classicalJointListener_fst_real_lt_iff_invPowSum (hsem : ∀ t, ∃ c, t ∈ sem c) {α : ℝ}
    (hα : 0 < α) {o : O} {t₁ t₂ : T} (h₂ : ∃ c, obs c = o ∧ t₂ ∈ sem c) :
    ((classicalJointListener sem obs α o).fst.real {t₁}
        < (classicalJointListener sem obs α o).fst.real {t₂})
      ↔ ((fiberProfile sem obs o t₁).invPowSum α).toReal * ((profile sem t₂).invPowSum α).toReal
        < ((fiberProfile sem obs o t₂).invPowSum α).toReal
            * ((profile sem t₁).invPowSum α).toReal := by
  obtain ⟨c₂, hc₂, hmem⟩ := h₂
  have hWne : ∀ t, (fiberProfile sem obs o t).invPowSum α ≠ ∞ := fun t =>
    Multiset.invPowSum_ne_top hα.le (zero_notMem_fiberProfile sem obs o t)
  have hZ0 : ∀ t, (profile sem t).invPowSum α ≠ 0 := fun t =>
    (Multiset.invPowSum_pos hα.le (profile_ne_zero sem hsem t)).ne'
  have hZne : ∀ t, (profile sem t).invPowSum α ≠ ∞ := fun t =>
    Multiset.invPowSum_ne_top hα.le (zero_notMem_profile sem t)
  have hμ0 : (uniformOn (Set.univ : Set T)) {t₂} ≠ 0 := by
    rw [uniformOn_univ, Measure.count_singleton]; simp
  have key : ∀ t : T,
      (∑ c ∈ Finset.univ.filter (obs · = o),
        (uniformOn (Set.univ : Set T)).real {t} * (classicalSpeaker sem α t).real {c})
        = ((uniformOn (Set.univ : Set T)) {t}
            * ((fiberProfile sem obs o t).invPowSum α / (profile sem t).invPowSum α)).toReal :=
    fun t => by
      rw [← Finset.mul_sum, measureReal_def,
        show (∑ c ∈ Finset.univ.filter (obs · = o), (classicalSpeaker sem α t).real {c})
          = ((fiberProfile sem obs o t).invPowSum α / (profile sem t).invPowSum α).toReal from by
          rw [← sum_fiber_classicalSpeaker sem obs hα,
            ENNReal.toReal_sum fun c _ => measure_ne_top _ _]
          simp_rw [measureReal_def],
        ENNReal.toReal_mul]
  rw [classicalJointListener, jointListener_fst_real_lt_iff _ _ _ _ _
      (map_comp_classicalSpeaker_ne_zero sem obs hα.le hc₂ hmem),
    key, key, show (uniformOn (Set.univ : Set T)) {t₁} = uniformOn Set.univ {t₂} from by
      rw [uniformOn_univ, uniformOn_univ, Measure.count_singleton, Measure.count_singleton],
    ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.div_ne_top (hWne t₁) (hZ0 t₁)))
      (ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.div_ne_top (hWne t₂) (hZ0 t₂))),
    ENNReal.mul_lt_mul_iff_right hμ0 (measure_ne_top _ _),
    ENNReal.div_lt_iff (Or.inl (hZ0 t₁)) (Or.inl (hZne t₁)),
    div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
    ENNReal.lt_div_iff_mul_lt (Or.inl (hZ0 t₂)) (Or.inl (hZne t₂)),
    ← ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (hWne t₁) (hZne t₂)) (ENNReal.mul_ne_top (hWne t₂) (hZne t₁)),
    ENNReal.toReal_mul, ENNReal.toReal_mul]

omit [Fintype T] [MeasurableSpace T] [DiscreteMeasurableSpace T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty T]
  [Nonempty C] in
/-- The certificate closes the odds comparison: strict domination of the fibre-by-rest cross
products decides it uniformly in the rationality (the shared fibre-by-fibre terms cancel). -/
theorem invPowSum_odds_lt_of_prodMul_strictDominates {α : ℝ} (hα : 0 < α) {o : O} {t₁ t₂ : T}
    (hcert : ((fiberProfile sem obs o t₂).prodMul (restProfile sem obs o t₁)).StrictDominates
      ((fiberProfile sem obs o t₁).prodMul (restProfile sem obs o t₂))) :
    ((fiberProfile sem obs o t₁).invPowSum α).toReal * ((profile sem t₂).invPowSum α).toReal
      < ((fiberProfile sem obs o t₂).invPowSum α).toReal
          * ((profile sem t₁).invPowSum α).toReal := by
  have hWne : ∀ t, (fiberProfile sem obs o t).invPowSum α ≠ ∞ := fun t =>
    Multiset.invPowSum_ne_top hα.le (zero_notMem_fiberProfile sem obs o t)
  have hodds : (fiberProfile sem obs o t₁).invPowSum α * (restProfile sem obs o t₂).invPowSum α
      < (fiberProfile sem obs o t₂).invPowSum α * (restProfile sem obs o t₁).invPowSum α := by
    rw [← Multiset.invPowSum_prodMul hα.le, ← Multiset.invPowSum_prodMul hα.le]
    exact hcert.invPowSum_lt hα
      (Multiset.zero_notMem_prodMul (zero_notMem_fiberProfile sem obs o t₁)
        (zero_notMem_restProfile sem obs o t₂))
  rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul,
    ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (hWne t₁)
        (Multiset.invPowSum_ne_top hα.le (zero_notMem_profile sem t₂)))
      (ENNReal.mul_ne_top (hWne t₂)
        (Multiset.invPowSum_ne_top hα.le (zero_notMem_profile sem t₁))),
    profile_eq_fiberProfile_add_restProfile sem obs o t₁,
    profile_eq_fiberProfile_add_restProfile sem obs o t₂, Multiset.invPowSum_add,
    Multiset.invPowSum_add, mul_add, mul_add, mul_comm ((fiberProfile sem obs o t₂).invPowSum α)]
  exact ENNReal.add_lt_add_left (ENNReal.mul_ne_top (hWne t₁) (hWne t₂)) hodds

/-- The certificate register: strict domination of the fibre-by-rest profile products
decides listener preference uniformly in the rationality. The certificate carries its own
truth witness, so a finding is a single decided `Multiset.StrictDominates` fact. An empty
fibre at `t₁` is the support case: any nonempty product strictly dominates `0`. -/
theorem classicalJointListener_fst_real_lt_of_prodMul_strictDominates
    (hsem : ∀ t, ∃ c, t ∈ sem c) {α : ℝ} (hα : 0 < α) {o : O} {t₁ t₂ : T}
    (hcert : ((fiberProfile sem obs o t₂).prodMul (restProfile sem obs o t₁)).StrictDominates
      ((fiberProfile sem obs o t₁).prodMul (restProfile sem obs o t₂))) :
    (classicalJointListener sem obs α o).fst.real {t₁}
      < (classicalJointListener sem obs α o).fst.real {t₂} :=
  (classicalJointListener_fst_real_lt_iff_invPowSum sem obs hsem hα
      (exists_of_fiberProfile_ne_zero sem obs fun h =>
        hcert.ne_zero (Multiset.prodMul_eq_zero_iff.mpr (Or.inl h)))).mpr
    (invPowSum_odds_lt_of_prodMul_strictDominates sem obs hα hcert)

/-- The evaluation register at a natural rationality: with all profile entries dividing `D`,
listener preference is the ℕ-valued common-denominator comparison — a kernel `decide`. The
strict inequality carries its own truth witness. -/
theorem classicalJointListener_fst_real_lt_of_divPowSum (hsem : ∀ t, ∃ c, t ∈ sem c) {k D : ℕ}
    [NeZero k] [NeZero D] {o : O} {t₁ t₂ : T}
    (hdvd₁ : ∀ n ∈ profile sem t₁, n ∣ D) (hdvd₂ : ∀ n ∈ profile sem t₂, n ∣ D)
    (hlt : (fiberProfile sem obs o t₁).divPowSum D k * (profile sem t₂).divPowSum D k
      < (fiberProfile sem obs o t₂).divPowSum D k * (profile sem t₁).divPowSum D k) :
    (classicalJointListener sem obs k o).fst.real {t₁}
      < (classicalJointListener sem obs k o).fst.real {t₂} := by
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hfsub : ∀ t, ∀ n ∈ fiberProfile sem obs o t, n ∈ profile sem t := fun t n hn =>
    profile_eq_fiberProfile_add_restProfile sem obs o t ▸ Multiset.mem_add.mpr (Or.inl hn)
  have h₂ : fiberProfile sem obs o t₂ ≠ 0 :=
    Multiset.ne_zero_of_divPowSum_ne_zero
      (Nat.mul_ne_zero_iff.mp (Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) hlt))).1
  rw [classicalJointListener_fst_real_lt_iff_invPowSum sem obs hsem hα
    (exists_of_fiberProfile_ne_zero sem obs h₂)]
  have key : ∀ (m₁ m₂ : Multiset ℕ), (∀ n ∈ m₁, n ∣ D) → (∀ n ∈ m₂, n ∣ D) →
      (m₁.invPowSum k).toReal * (m₂.invPowSum k).toReal
        = (m₁.divPowSum D k * m₂.divPowSum D k : ℕ) / ((D : ℝ) ^ k) ^ 2 := by
    intro m₁ m₂ h₁ h₂
    rw [Multiset.invPowSum_toReal_eq (NeZero.ne D) k h₁,
      Multiset.invPowSum_toReal_eq (NeZero.ne D) k h₂]
    push_cast
    ring
  rw [key _ _ (fun n hn => hdvd₁ n (hfsub t₁ n hn)) hdvd₂,
    key _ _ (fun n hn => hdvd₂ n (hfsub t₂ n hn)) hdvd₁,
    div_lt_div_iff_of_pos_right (by have := NeZero.ne D; positivity)]
  exact_mod_cast hlt

end Classical

end RSA
