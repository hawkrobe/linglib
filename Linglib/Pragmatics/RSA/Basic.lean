import Mathlib.Probability.Kernel.Posterior
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# The Rational Speech Act pipeline on probability kernels

The basic RSA model ([frank-goodman-2012]; [degen-2023] eqs. 1–4) in mathlib's
probability vocabulary. The literal listener conditions the prior on the
utterance's extension (`ProbabilityTheory.cond`); the pragmatic speaker is the
softmax of an `EReal`-valued utility, packaged as a Markov kernel; and the
pragmatic listener is the Bayesian inverse of the speaker — mathlib's
posterior kernel `κ†μ`, not a new definition. Predictions are stated on reals
via `Measure.real`.

## Main definitions

* `RSA.literalListener` — eq. 1: the prior conditioned on the extension.
* `RSA.utility` — eq. 3: informativity minus cost.
* `RSA.speaker` — eq. 2: the softmax-utility speaker, as a kernel built by
  `ProbabilityTheory.Kernel.ofWeights`.

## Main statements

* `ProbabilityTheory.posterior_apply_singleton` — exact Bayes for `κ†μ` at a
  positive-mass observation.
* `ProbabilityTheory.posterior_real_singleton_lt_iff` — pragmatic-listener
  preference on reals reduces to prior-weighted speaker masses.
* `RSA.speaker_real_singleton_lt_iff` — speaker preference reduces to utility
  comparison.

## Implementation notes

All spaces here are finite and discrete; the ⊤ σ-algebra makes every study
enum standard Borel, so mathlib's disintegration-based posterior applies. Its
characterization is almost-everywhere, but an ae-fact holds at every atom of
positive mass (`MeasureTheory.ae_of_singleton_ne_zero`), which yields exact
Bayes pointwise — no `rnDeriv`. An inapplicable utterance has utility `⊥`
(weight `0`); `α = 0` gives the uniform speaker since `(0 : EReal) * ⊥ = 0`.
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

/-- Weight-kernel rows are subprobabilities: normalization gives mass 1 on
positive finite total weight and 0 otherwise. -/
instance (w : α → β → ℝ≥0∞) : IsFiniteKernel (ofWeights w) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun a => ?_⟩⟩
  show ((∑ b, w a b)⁻¹ • ∑ b, w a b • Measure.dirac b) Set.univ ≤ 1
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rcases eq_or_ne (∑ b, w a b) 0 with h0 | h0
  · simp [h0]
  · rcases eq_or_ne (∑ b, w a b) ∞ with htop | htop
    · simp [htop]
    · rw [ENNReal.inv_mul_cancel h0 htop]

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

/-- Pragmatic-listener preference on reals reduces to comparing
prior-weighted speaker masses on reals; the observation's marginal cancels. -/
theorem posterior_real_singleton_lt_iff {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0)
    (ω₁ ω₂ : Ω) :
    ((κ†μ) x).real {ω₁} < ((κ†μ) x).real {ω₂}
      ↔ μ.real {ω₁} * (κ ω₁).real {x} < μ.real {ω₂} * (κ ω₂).real {x} := by
  rw [measureReal_def, measureReal_def, posterior_apply_singleton κ μ hx,
    posterior_apply_singleton κ μ hx,
    ENNReal.toReal_lt_toReal
      (ENNReal.div_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) hx)
      (ENNReal.div_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) hx),
    ENNReal.div_lt_div_iff_left hx (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  exact Iff.rfl

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

/-- Witness form of the observation-marginal positivity for pair emissions:
one state with positive prior mass and positive mass on one (observed,
latent) pair. -/
theorem map_fst_comp_apply_singleton_ne_zero {Ω' 𝓧' Θ' : Type*}
    [MeasurableSpace Ω'] [MeasurableSpace 𝓧'] [MeasurableSpace Θ']
    [MeasurableSingletonClass 𝓧'] [MeasurableSingletonClass Θ']
    (κ : Kernel Ω' (𝓧' × Θ')) (μ : Measure Ω') {w : Ω'} {x : 𝓧'} {θ : Θ'}
    (hμ : μ {w} ≠ 0) (hκ : κ w {(x, θ)} ≠ 0) :
    ((κ ∘ₘ μ).map Prod.fst) {x} ≠ 0 := by
  rw [Measure.map_apply measurable_fst (.singleton x)]
  refine fun h => comp_apply_singleton_ne_zero κ μ hμ hκ (measure_mono_null ?_ h)
  exact Set.singleton_subset_iff.mpr rfl

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

end ProbabilityTheory

/-! ### Joint posteriors from partially observed pairs

When a kernel emits a pair of which only the first component is observed —
RSA's intention models, where the speaker chooses an (utterance, latent) pair
and the listener hears only the utterance — the listener's joint posterior
over parameter and latent is the conditional kernel of the reassociated
joint: the same construction as `ProbabilityTheory.posterior` with a
reassociation in place of the swap. (When the latent is instead part of the
state, the joint posterior is plain `κ†μ` at a product parameter space.) -/

namespace ProbabilityTheory

variable {Ω 𝓧 Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧] [MeasurableSpace Θ]
  [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Θ] [Nonempty Θ]
  (κ : Kernel Ω (𝓧 × Θ)) (μ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteKernel κ]

omit [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Θ] [Nonempty Θ] in
lemma measurable_jointReassoc :
    Measurable fun p : Ω × (𝓧 × Θ) => (p.2.1, (p.1, p.2.2)) :=
  (measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

/-- The distribution of the observed component paired with (parameter,
latent). -/
noncomputable def jointObs : Measure (𝓧 × (Ω × Θ)) :=
  (μ ⊗ₘ κ).map fun p => (p.2.1, (p.1, p.2.2))

instance : IsFiniteMeasure (jointObs κ μ) :=
  inferInstanceAs (IsFiniteMeasure ((μ ⊗ₘ κ).map _))

omit [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Θ] [Nonempty Θ] in
/-- The observed component of the joint is distributed as the data marginal. -/
theorem jointObs_fst : (jointObs κ μ).fst = ((κ ∘ₘ μ).map Prod.fst) := by
  rw [jointObs, Measure.fst,
    Measure.map_map measurable_fst measurable_jointReassoc,
    show (Prod.fst ∘ fun p : Ω × (𝓧 × Θ) => (p.2.1, (p.1, p.2.2)))
      = Prod.fst ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_fst measurable_snd, ← Measure.snd,
    Measure.snd_compProd]

/-- The joint posterior over parameter and latent, given the observed first
component of a jointly chosen pair ([franke-bergen-2020]'s intention
listeners; the marginalization step of [degen-2023]'s latent-variable
extensions). -/
noncomputable def jointPosterior : Kernel 𝓧 (Ω × Θ) :=
  (jointObs κ μ).condKernel

instance : IsMarkovKernel (jointPosterior κ μ) :=
  inferInstanceAs (IsMarkovKernel (jointObs κ μ).condKernel)

variable [MeasurableSingletonClass Ω] [MeasurableSingletonClass 𝓧]
  [MeasurableSingletonClass Θ]

/-- Exact Bayes for the joint posterior at a positive-mass observation. -/
theorem jointPosterior_apply_singleton {x : 𝓧}
    (hx : ((κ ∘ₘ μ).map Prod.fst) {x} ≠ 0) (ω : Ω) (θ : Θ) :
    jointPosterior κ μ x {(ω, θ)}
      = μ {ω} * κ ω {(x, θ)} / ((κ ∘ₘ μ).map Prod.fst) {x} := by
  have hd := congrArg (fun m => m ({x} ×ˢ {(ω, θ)}))
    ((jointObs κ μ).disintegrate (jointObs κ μ).condKernel)
  beta_reduce at hd
  rw [Measure.compProd_apply_prod (.singleton x) (.singleton (ω, θ)),
    lintegral_singleton, jointObs_fst] at hd
  unfold jointObs at hd
  rw [Measure.map_apply measurable_jointReassoc
      ((MeasurableSet.singleton x).prod (.singleton (ω, θ))),
    show (fun p : Ω × (𝓧 × Θ) => (p.2.1, (p.1, p.2.2))) ⁻¹' ({x} ×ˢ {(ω, θ)})
        = {ω} ×ˢ {(x, θ)} from by
      ext ⟨a, b, c⟩
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Prod.ext_iff]
      tauto,
    Measure.compProd_apply_prod (.singleton ω) (.singleton (x, θ)),
    lintegral_singleton] at hd
  rw [jointPosterior, ENNReal.eq_div_iff hx (measure_ne_top _ _), mul_comm]
  unfold jointObs
  rw [hd]
  ring

/-- Parameter preference under the joint posterior, on reals: the
observation's marginal cancels, leaving prior-weighted pooled pair masses. -/
theorem jointPosterior_fst_real_lt_iff [Fintype Θ] {x : 𝓧}
    (hx : ((κ ∘ₘ μ).map Prod.fst) {x} ≠ 0) (ω₁ ω₂ : Ω) :
    (jointPosterior κ μ x).fst.real {ω₁} < (jointPosterior κ μ x).fst.real {ω₂}
      ↔ (∑ θ, μ.real {ω₁} * (κ ω₁).real {(x, θ)})
          < ∑ θ, μ.real {ω₂} * (κ ω₂).real {(x, θ)} := by
  have hne : ∀ ω, (∑ θ, μ {ω} * κ ω {(x, θ)}) ≠ ∞ := fun ω =>
    ENNReal.sum_ne_top.mpr fun θ _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, Measure.fst_apply_singleton,
    Measure.fst_apply_singleton]
  simp_rw [jointPosterior_apply_singleton κ μ hx, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne ω₁) hx) (ENNReal.div_ne_top (hne ω₂) hx),
    ENNReal.div_lt_div_iff_left hx (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne ω₁) (hne ω₂),
    ENNReal.toReal_sum (fun θ _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun θ _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

/-- Latent preference under the joint posterior, on reals. -/
theorem jointPosterior_snd_real_lt_iff [Fintype Ω] {x : 𝓧}
    (hx : ((κ ∘ₘ μ).map Prod.fst) {x} ≠ 0) (θ₁ θ₂ : Θ) :
    (jointPosterior κ μ x).snd.real {θ₁} < (jointPosterior κ μ x).snd.real {θ₂}
      ↔ (∑ ω, μ.real {ω} * (κ ω).real {(x, θ₁)})
          < ∑ ω, μ.real {ω} * (κ ω).real {(x, θ₂)} := by
  have hne : ∀ θ, (∑ ω, μ {ω} * κ ω {(x, θ)}) ≠ ∞ := fun θ =>
    ENNReal.sum_ne_top.mpr fun ω _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, Measure.snd_apply_singleton,
    Measure.snd_apply_singleton]
  simp_rw [jointPosterior_apply_singleton κ μ hx, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne θ₁) hx) (ENNReal.div_ne_top (hne θ₂) hx),
    ENNReal.div_lt_div_iff_left hx (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne θ₁) (hne θ₂),
    ENNReal.toReal_sum (fun ω _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun ω _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

end ProbabilityTheory

/-! ### The RSA pipeline -/

namespace RSA

variable {W U : Type*} [MeasurableSpace W] [MeasurableSpace U]
  [Fintype W] [MeasurableSingletonClass W]
  [Fintype U] [MeasurableSingletonClass U]

/-- The literal listener (eq. 1): the prior belief conditioned on the
utterance's extension. -/
noncomputable def literalListener (μ : Measure W) (sem : U → Set W) : Kernel U W :=
  Kernel.ofFunOfCountable fun u => μ[|sem u]

theorem literalListener_apply (μ : Measure W) (sem : U → Set W) (u : U) (t : Set W) :
    literalListener μ sem u t = (μ (sem u))⁻¹ * μ (sem u ∩ t) := by
  rw [literalListener, Kernel.ofFunOfCountable, Kernel.coe_mk]
  exact cond_apply .of_discrete μ t

/-- On a positive-mass extension, the literal listener is the renormalized
prior at members … -/
theorem literalListener_apply_singleton_of_mem (μ : Measure W) (sem : U → Set W)
    {u : U} {w : W} (h : w ∈ sem u) :
    literalListener μ sem u {w} = (μ (sem u))⁻¹ * μ {w} := by
  rw [literalListener_apply, Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)]

/-- … and zero at non-members: literal falsity is never entertained. -/
theorem literalListener_apply_singleton_of_not_mem (μ : Measure W) (sem : U → Set W)
    {u : U} {w : W} (h : w ∉ sem u) :
    literalListener μ sem u {w} = 0 := by
  rw [literalListener_apply, Set.inter_comm, Set.singleton_inter_eq_empty.mpr h]
  simp

omit [Fintype W] [MeasurableSingletonClass W] in
/-- The literal listener is Markov as soon as every extension has positive
prior mass. -/
theorem isMarkovKernel_literalListener (μ : Measure W) [IsFiniteMeasure μ]
    (sem : U → Set W) (h : ∀ u, μ (sem u) ≠ 0) :
    IsMarkovKernel (literalListener μ sem) := by
  refine ⟨fun u => ?_⟩
  rw [literalListener, Kernel.ofFunOfCountable, Kernel.coe_mk]
  exact cond_isProbabilityMeasure (h u)

/-- Speaker utility (eq. 3): informativity minus cost, valued in `EReal` so
that a literally false utterance (`L0 = 0`) has utility `⊥`. -/
noncomputable def utility (L0 : Kernel U W) (cost : U → ℝ) (w : W) (u : U) : EReal :=
  ENNReal.log (L0 u {w}) - (cost u : EReal)

/-- The pragmatic speaker (eq. 2): the softmax of the utility at rationality
`α`, as a kernel from worlds to utterances. -/
noncomputable def speaker (α : ℝ) (util : W → U → EReal) : Kernel W U :=
  Kernel.ofWeights fun w u => ((α : EReal) * util w u).exp

@[simp] theorem speaker_apply_singleton (α : ℝ) (util : W → U → EReal) (w : W) (u : U) :
    speaker α util w {u} = ((α : EReal) * util w u).exp / ∑ u', ((α : EReal) * util w u').exp :=
  Kernel.ofWeights_apply_singleton _ w u

/-- An utterance of utility `⊥` is never produced. -/
theorem speaker_apply_singleton_eq_zero {α : ℝ} {util : W → U → EReal} {w : W} {u : U}
    (hbot : (α : EReal) * util w u = ⊥) : speaker α util w {u} = 0 := by
  rw [speaker_apply_singleton, hbot, EReal.exp_bot, ENNReal.zero_div]

/-- Real form of `speaker_apply_singleton_eq_zero`. -/
theorem speaker_real_singleton_eq_zero {α : ℝ} {util : W → U → EReal} {w : W} {u : U}
    (hbot : (α : EReal) * util w u = ⊥) : (speaker α util w).real {u} = 0 := by
  rw [measureReal_def, speaker_apply_singleton_eq_zero hbot, ENNReal.toReal_zero]

/-- A speaker mass is positive as soon as the utterance's scaled utility is
not `⊥` and no scaled utility is `⊤`. -/
theorem speaker_apply_singleton_ne_zero {α : ℝ} {util : W → U → EReal} {w : W} {u : U}
    (hbot : (α : EReal) * util w u ≠ ⊥) (htop : ∀ u', (α : EReal) * util w u' ≠ ⊤) :
    speaker α util w {u} ≠ 0 := by
  rw [speaker_apply_singleton, ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by simp [EReal.exp_eq_zero_iff, hbot],
    ENNReal.sum_ne_top.mpr fun u' _ => by simp [EReal.exp_eq_top_iff, htop u']⟩

/-- A speaker mass is positive on reals as soon as the utterance's scaled
utility is not `⊥` and no scaled utility is `⊤`. -/
theorem speaker_real_singleton_pos {α : ℝ} {util : W → U → EReal} {w : W} {u : U}
    (hbot : (α : EReal) * util w u ≠ ⊥) (htop : ∀ u', (α : EReal) * util w u' ≠ ⊤) :
    0 < (speaker α util w).real {u} := by
  rw [measureReal_def]
  refine ENNReal.toReal_pos (speaker_apply_singleton_ne_zero hbot htop) ?_
  rw [speaker_apply_singleton]
  exact ENNReal.div_ne_top (by simp [EReal.exp_eq_top_iff, htop u]) fun hz =>
    hbot (by simpa [EReal.exp_eq_zero_iff] using
      Finset.sum_eq_zero_iff.mp hz u (Finset.mem_univ u))

omit [MeasurableSingletonClass U] in
/-- The speaker is Markov as soon as no scaled utility is `⊤` and every
world has an applicable (scaled utility `≠ ⊥`) utterance. -/
theorem isMarkovKernel_speaker {α : ℝ} {util : W → U → EReal}
    (htop : ∀ w u, (α : EReal) * util w u ≠ ⊤)
    (hwit : ∀ w, ∃ u, (α : EReal) * util w u ≠ ⊥) :
    IsMarkovKernel (speaker α util) :=
  Kernel.isMarkovKernel_ofWeights
    (fun w => (hwit w).imp fun u hu => by simp [EReal.exp_eq_zero_iff, hu])
    (fun w u => by simp [EReal.exp_eq_top_iff, htop w u])

omit [Fintype W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U] in
/-- The cost-free informativity speaker reduces to power weights: the softmax
weight at `utility L0 0` is `L0^α` — the specialization every exact-zeros
study instantiates. -/
theorem exp_mul_utility_zero (α : ℝ) (L0 : Kernel U W) (w : W) (u : U) :
    ((α : EReal) * utility L0 (fun _ => 0) w u).exp = L0 u {w} ^ α := by
  rw [utility, EReal.coe_zero, sub_zero, ← ENNReal.log_rpow, ENNReal.exp_log]

/-- The literal listener never takes the value `⊤`: a null extension nulls
the numerator too. -/
theorem literalListener_apply_ne_top (μ : Measure W) [IsFiniteMeasure μ]
    (sem : U → Set W) (u : U) (t : Set W) :
    literalListener μ sem u t ≠ ∞ := by
  rw [literalListener_apply]
  rcases eq_or_ne (μ (sem u)) 0 with h | h
  · rw [measure_mono_null Set.inter_subset_left h, mul_zero]
    exact ENNReal.zero_ne_top
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr h) (measure_ne_top _ _)

/-- The literal listener on reals: the renormalized prior. -/
theorem literalListener_real_singleton_of_mem (μ : Measure W) [IsFiniteMeasure μ]
    {sem : U → Set W} {u : U} {w : W} (h : w ∈ sem u) :
    (literalListener μ sem u).real {w} = μ.real {w} / μ.real (sem u) := by
  rw [measureReal_def, literalListener_apply_singleton_of_mem μ sem h,
    ENNReal.toReal_mul, ENNReal.toReal_inv, measureReal_def, measureReal_def,
    inv_mul_eq_div]

theorem literalListener_real_singleton_of_not_mem (μ : Measure W)
    {sem : U → Set W} {u : U} {w : W} (h : w ∉ sem u) :
    (literalListener μ sem u).real {w} = 0 := by
  rw [measureReal_def, literalListener_apply_singleton_of_not_mem μ sem h,
    ENNReal.toReal_zero]

/-- A member of a finite-mass extension with positive prior mass has positive
literal-listener mass. -/
theorem literalListener_apply_singleton_ne_zero (μ : Measure W) [IsFiniteMeasure μ]
    {sem : U → Set W} {u : U} {w : W} (h : w ∈ sem u) (hw : μ {w} ≠ 0) :
    literalListener μ sem u {w} ≠ 0 := by
  rw [literalListener_apply_singleton_of_mem μ sem h]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hw

/-- `(α : EReal) * ENNReal.log x` is bounded above for nonnegative real `α`
and `x ≠ ⊤` (migrating here from the PMF softmax stack). -/
theorem coe_mul_log_ne_top {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    ((α : EReal) * ENNReal.log x) ≠ ⊤ := by
  rw [EReal.mul_ne_top]
  exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inl (EReal.coe_nonneg.mpr hα),
    Or.inl (EReal.coe_ne_top _), Or.inr fun h => hx (ENNReal.log_eq_top_iff.mp h)⟩

/-- `(α : EReal) * ENNReal.log x` is bounded below for nonnegative real `α`
and `x ≠ 0`. -/
theorem coe_mul_log_ne_bot {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hx : x ≠ 0) :
    ((α : EReal) * ENNReal.log x) ≠ ⊥ := by
  rw [EReal.mul_ne_bot]
  exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inr fun h => hx (ENNReal.log_eq_bot_iff.mp h),
    Or.inl (EReal.coe_ne_top _), Or.inl (EReal.coe_nonneg.mpr hα)⟩

omit [MeasurableSingletonClass U] in
/-- The cost-free informativity speaker is Markov given a nonnegative
rationality, finite literal-listener values, and an applicable utterance per
world. -/
theorem isMarkovKernel_speaker_utility_zero {α : ℝ} (hα : 0 ≤ α) {L0 : Kernel U W}
    (htop : ∀ u w, L0 u {w} ≠ ∞) (hwit : ∀ w, ∃ u, L0 u {w} ≠ 0) :
    IsMarkovKernel (speaker α (utility L0 fun _ => 0)) := by
  refine isMarkovKernel_speaker (fun w u => ?_) fun w => (hwit w).imp fun u hu => ?_
  · rw [utility, EReal.coe_zero, sub_zero]
    exact coe_mul_log_ne_top hα (htop u w)
  · rw [utility, EReal.coe_zero, sub_zero]
    exact coe_mul_log_ne_bot hα hu

/-- The cost-free informativity speaker on reals: normalized powers of the
literal listener. -/
theorem speaker_utility_zero_real_singleton {α : ℝ} (hα : 0 ≤ α) (L0 : Kernel U W)
    {w : W} (htop : ∀ u', L0 u' {w} ≠ ∞) (u : U) :
    (speaker α (utility L0 fun _ => 0) w).real {u}
      = (L0 u {w}).toReal ^ α / ∑ u', (L0 u' {w}).toReal ^ α := by
  rw [measureReal_def, speaker_apply_singleton]
  simp_rw [exp_mul_utility_zero]
  rw [ENNReal.toReal_div,
    ENNReal.toReal_sum fun u' _ => ENNReal.rpow_ne_top_of_nonneg hα (htop u')]
  simp_rw [ENNReal.toReal_rpow]

/-! ### The bundled speaker

`RSA.Speaker` packages the theory's data — a rationality, a prior, and a
semantics — and derives the pipeline: `S.L0` conditions the prior on an
utterance's extension, `S.toKernel` is the softmax-informativity speaker, and
the listeners are its Bayesian inverses. Its API states facts at the semantic
level (membership in extensions), so EReal utilities never surface in
studies; standing side conditions are the typeclasses `Speaker.Viable` and
`Speaker.Positive`. -/

variable (W U) in
/-- A cost-free informativity speaker: rationality, prior beliefs, and a
truth-conditional semantics. -/
structure Speaker where
  /-- The softmax rationality (Degen's α). -/
  α : ℝ
  /-- Rationality is positive: at `α = 0` the speaker is uniformly random and
  support is no longer literal truth. -/
  α_pos : 0 < α
  /-- Prior beliefs about worlds. -/
  prior : Measure W
  /-- The semantics: each utterance's extension. -/
  sem : U → Set W

namespace Speaker

section
variable (S : Speaker W U)

/-- The literal listener (eq. 1). -/
noncomputable def L0 : Kernel U W := literalListener S.prior S.sem

/-- The speaker kernel (eq. 2 at the informativity utility of eq. 3). -/
noncomputable def toKernel : Kernel W U := speaker S.α (utility S.L0 fun _ => 0)

/-- Every world has a true utterance. -/
class Viable : Prop where
  exists_mem : ∀ w, ∃ u, w ∈ S.sem u

/-- The prior gives every world positive mass. -/
class Positive : Prop where
  prior_ne_zero : ∀ w, S.prior {w} ≠ 0

variable [IsFiniteMeasure S.prior]

omit [MeasurableSpace U] [Fintype W] [MeasurableSingletonClass W] [Fintype U]
  [MeasurableSingletonClass U] in
theorem prior_real_pos [S.Positive] (w : W) : 0 < S.prior.real {w} :=
  ENNReal.toReal_pos (Positive.prior_ne_zero w) (measure_ne_top _ _)

theorem L0_apply_singleton_ne_zero [S.Positive] {u : U} {w : W} (h : w ∈ S.sem u) :
    S.L0 u {w} ≠ 0 :=
  literalListener_apply_singleton_ne_zero S.prior h (Positive.prior_ne_zero w)

private theorem scaled_utility_ne_top (w : W) (u : U) :
    (S.α : EReal) * utility S.L0 (fun _ => 0) w u ≠ ⊤ := by
  rw [utility, EReal.coe_zero, sub_zero]
  exact coe_mul_log_ne_top S.α_pos.le (literalListener_apply_ne_top S.prior _ u {w})

instance [S.Viable] [S.Positive] : IsMarkovKernel S.toKernel :=
  isMarkovKernel_speaker_utility_zero S.α_pos.le
    (fun u w => literalListener_apply_ne_top S.prior _ u {w})
    fun w => (Viable.exists_mem (S := S) w).imp fun _ h => S.L0_apply_singleton_ne_zero h

/-- The speaker's support is literal truth: an utterance gets positive mass
exactly on its extension. -/
@[simp] theorem toKernel_real_singleton_pos_iff [S.Positive] (w : W) (u : U) :
    0 < (S.toKernel w).real {u} ↔ w ∈ S.sem u := by
  constructor
  · intro h
    by_contra hmem
    rw [toKernel, speaker_real_singleton_eq_zero (by
      rw [utility, EReal.coe_zero, sub_zero, L0,
        literalListener_apply_singleton_of_not_mem S.prior _ hmem, ENNReal.log_zero]
      exact EReal.mul_bot_of_pos (by exact_mod_cast S.α_pos))] at h
    exact lt_irrefl 0 h
  · intro h
    exact speaker_real_singleton_pos
      (by
        rw [utility, EReal.coe_zero, sub_zero]
        exact coe_mul_log_ne_bot S.α_pos.le (S.L0_apply_singleton_ne_zero h))
      (S.scaled_utility_ne_top w)

/-- An utterance outside its extension is never produced. -/
theorem toKernel_real_singleton_eq_zero [S.Positive] {w : W} {u : U} (h : w ∉ S.sem u) :
    (S.toKernel w).real {u} = 0 := by
  by_contra hne
  exact h ((S.toKernel_real_singleton_pos_iff w u).mp
    (lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)))

/-- A true utterance is produced with positive mass. -/
theorem toKernel_apply_singleton_ne_zero [S.Positive] {w : W} {u : U} (h : w ∈ S.sem u) :
    S.toKernel w {u} ≠ 0 := by
  intro h0
  have hpos := (S.toKernel_real_singleton_pos_iff w u).mpr h
  rw [measureReal_def, h0] at hpos
  simp at hpos

section Listener

variable [StandardBorelSpace W] [Nonempty W] [S.Viable] [S.Positive]

/-- The pragmatic listener (eq. 4): the Bayesian inverse of the speaker. -/
noncomputable def listener : Kernel U W := S.toKernel†S.prior

/-- Pragmatic-listener preference reduces to comparing prior-weighted speaker
masses; the observation's marginal cancels. -/
theorem listener_real_singleton_lt_iff {u : U} (hu : (S.toKernel ∘ₘ S.prior) {u} ≠ 0)
    (w₁ w₂ : W) :
    (S.listener u).real {w₁} < (S.listener u).real {w₂}
      ↔ S.prior.real {w₁} * (S.toKernel w₁).real {u}
        < S.prior.real {w₂} * (S.toKernel w₂).real {u} :=
  posterior_real_singleton_lt_iff _ _ hu w₁ w₂

/-- Support preference: hearing `u`, the pragmatic listener strictly prefers a
world in `u`'s extension over one outside it. The truth of `u` at `w₂` also
witnesses the positive observation marginal. -/
theorem listener_real_singleton_lt_of_support {u : U} {w₁ w₂ : W}
    (h₁ : w₁ ∉ S.sem u) (h₂ : w₂ ∈ S.sem u) :
    (S.listener u).real {w₁} < (S.listener u).real {w₂} := by
  rw [listener, posterior_real_singleton_lt_iff _ _
      (comp_apply_singleton_ne_zero _ _ (Positive.prior_ne_zero w₂) (S.toKernel_apply_singleton_ne_zero h₂)),
    S.toKernel_real_singleton_eq_zero h₁, mul_zero]
  exact mul_pos (S.prior_real_pos w₂) ((S.toKernel_real_singleton_pos_iff w₂ u).mpr h₂)

end Listener

end

section Joint

variable {X Θ : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]
  [MeasurableSpace Θ] [Fintype Θ] [MeasurableSingletonClass Θ]
  [StandardBorelSpace Θ] [Nonempty Θ] [StandardBorelSpace W] [Nonempty W]
  (S : Speaker W (X × Θ)) [IsFiniteMeasure S.prior] [S.Viable] [S.Positive]

/-- The joint pragmatic listener over world and latent, given the heard
utterance ([franke-bergen-2020]'s intention listeners). -/
noncomputable def jointListener : Kernel X (W × Θ) := jointPosterior S.toKernel S.prior

/-- World preference under the joint listener reduces to comparing
prior-weighted pooled pair masses. -/
theorem jointListener_fst_real_lt_iff {x : X}
    (hx : ((S.toKernel ∘ₘ S.prior).map Prod.fst) {x} ≠ 0) (w₁ w₂ : W) :
    (S.jointListener x).fst.real {w₁} < (S.jointListener x).fst.real {w₂}
      ↔ (∑ θ, S.prior.real {w₁} * (S.toKernel w₁).real {(x, θ)})
        < ∑ θ, S.prior.real {w₂} * (S.toKernel w₂).real {(x, θ)} :=
  jointPosterior_fst_real_lt_iff _ _ hx w₁ w₂

/-- Latent preference under the joint listener reduces to comparing
prior-weighted per-world masses. -/
theorem jointListener_snd_real_lt_iff {x : X}
    (hx : ((S.toKernel ∘ₘ S.prior).map Prod.fst) {x} ≠ 0) (θ₁ θ₂ : Θ) :
    (S.jointListener x).snd.real {θ₁} < (S.jointListener x).snd.real {θ₂}
      ↔ (∑ w, S.prior.real {w} * (S.toKernel w).real {(x, θ₁)})
        < ∑ w, S.prior.real {w} * (S.toKernel w).real {(x, θ₂)} :=
  jointPosterior_snd_real_lt_iff _ _ hx θ₁ θ₂

/-- World preference by support: if no latent verifies the heard utterance at
`w₁` and some latent verifies it at `w₂`, the joint listener's world marginal
strictly prefers `w₂`. -/
theorem jointListener_fst_real_lt_of_support {x : X} {w₁ w₂ : W}
    (h₁ : ∀ θ, w₁ ∉ S.sem (x, θ)) (h₂ : ∃ θ, w₂ ∈ S.sem (x, θ)) :
    (S.jointListener x).fst.real {w₁} < (S.jointListener x).fst.real {w₂} := by
  obtain ⟨θ₂, h₂⟩ := h₂
  rw [jointListener, jointPosterior_fst_real_lt_iff _ _
      (map_fst_comp_apply_singleton_ne_zero _ _ (Positive.prior_ne_zero w₂)
        (S.toKernel_apply_singleton_ne_zero h₂)),
    Finset.sum_congr rfl fun θ _ => by rw [S.toKernel_real_singleton_eq_zero (h₁ θ), mul_zero],
    Finset.sum_const_zero]
  exact Finset.sum_pos' (fun θ _ => mul_nonneg measureReal_nonneg measureReal_nonneg)
    ⟨θ₂, Finset.mem_univ _,
      mul_pos (S.prior_real_pos w₂) ((S.toKernel_real_singleton_pos_iff w₂ (x, θ₂)).mpr h₂)⟩

/-- Latent preference by support: if no world verifies the heard utterance
under `θ₁` and some world of positive prior mass verifies it under `θ₂`, the
joint listener's latent marginal strictly prefers `θ₂`. -/
theorem jointListener_snd_real_lt_of_support {x : X} {θ₁ θ₂ : Θ}
    (h₁ : ∀ w, w ∉ S.sem (x, θ₁)) (h₂ : ∃ w, w ∈ S.sem (x, θ₂)) :
    (S.jointListener x).snd.real {θ₁} < (S.jointListener x).snd.real {θ₂} := by
  obtain ⟨w₂, h₂⟩ := h₂
  rw [jointListener, jointPosterior_snd_real_lt_iff _ _
      (map_fst_comp_apply_singleton_ne_zero _ _ (Positive.prior_ne_zero w₂)
        (S.toKernel_apply_singleton_ne_zero h₂)),
    Finset.sum_congr rfl fun w _ => by rw [S.toKernel_real_singleton_eq_zero (h₁ w), mul_zero],
    Finset.sum_const_zero]
  exact Finset.sum_pos' (fun w _ => mul_nonneg measureReal_nonneg measureReal_nonneg)
    ⟨w₂, Finset.mem_univ _,
      mul_pos (S.prior_real_pos w₂) ((S.toKernel_real_singleton_pos_iff w₂ (x, θ₂)).mpr h₂)⟩

end Joint

end Speaker

/-- Speaker preference on reals is utility comparison (eq. 2's softmax is
strictly monotone; the partition function cancels). -/
theorem speaker_real_singleton_lt_iff {α : ℝ} {util : W → U → EReal} (w : W)
    (h0 : (∑ u, ((α : EReal) * util w u).exp) ≠ 0)
    (hZtop : (∑ u, ((α : EReal) * util w u).exp) ≠ ∞) (u₁ u₂ : U) :
    (speaker α util w).real {u₁} < (speaker α util w).real {u₂}
      ↔ (α : EReal) * util w u₁ < (α : EReal) * util w u₂ := by
  rw [speaker, Kernel.ofWeights_real_singleton_lt_iff w h0 hZtop, EReal.exp_lt_exp_iff]

/-! ### The best-response speaker in power-weight form

[franke-bergen-2020] eq. 6 ≡ eq. 7: softmax of `α · log L` is, in weight
form, `L ^ α`. On `ℝ≥0∞` the power is total — an inapplicable utterance has
weight `0 ^ α = 0` — so falsity needs no `EReal` utilities and no `⊥`/`⊤`
side conditions. -/

private theorem weight_rpow_ne_zero {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hx : x ≠ 0) :
    x ^ α ≠ 0 := by
  rw [ne_eq, ENNReal.rpow_eq_zero_iff, not_or]
  exact ⟨fun h => hx h.1, fun h => absurd hα (not_le.mpr h.2)⟩

private theorem weight_rpow_ne_top {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hle : x ≤ 1) :
    x ^ α ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (ENNReal.one_rpow α ▸ ENNReal.rpow_le_rpow hle hα)

/-- The best-response speaker to a listener kernel: power weights
`L u {w} ^ α` ([franke-bergen-2020] eq. 7, [degen-2023] eq. 2 at the
informativity utility). -/
noncomputable def speakerOf (α : ℝ) (L : Kernel U W) : Kernel W U :=
  Kernel.ofWeights fun w u => L u {w} ^ α

@[simp] theorem speakerOf_apply_singleton (α : ℝ) (L : Kernel U W) (w : W) (u : U) :
    speakerOf α L w {u} = L u {w} ^ α / ∑ u', L u' {w} ^ α :=
  Kernel.ofWeights_apply_singleton _ w u

instance (α : ℝ) (L : Kernel U W) : IsFiniteKernel (speakerOf α L) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

omit [MeasurableSingletonClass U] in
/-- The speaker is a probability kernel whenever every state has a true
utterance ([franke-bergen-2020] eq. 7's proviso). -/
theorem isMarkovKernel_speakerOf {α : ℝ} (hα : 0 ≤ α) (L : Kernel U W)
    (hle : ∀ u w, L u {w} ≤ 1) (h0 : ∀ w, ∃ u, L u {w} ≠ 0) :
    IsMarkovKernel (speakerOf α L) :=
  Kernel.isMarkovKernel_ofWeights
    (fun w => (h0 w).imp fun _ hu => weight_rpow_ne_zero hα hu)
    fun w u => weight_rpow_ne_top hα (hle u w)

/-- A literally false utterance is never produced (positive rationality). -/
theorem speakerOf_apply_singleton_eq_zero {α : ℝ} (hα : 0 < α) {L : Kernel U W}
    {w : W} {u : U} (h : L u {w} = 0) : speakerOf α L w {u} = 0 := by
  rw [speakerOf_apply_singleton, h, ENNReal.zero_rpow_of_pos hα, ENNReal.zero_div]

/-- A literally true utterance is produced with positive mass. -/
theorem speakerOf_apply_singleton_ne_zero {α : ℝ} (hα : 0 ≤ α) {L : Kernel U W}
    {w : W} (hle : ∀ u', L u' {w} ≤ 1) {u : U} (h : L u {w} ≠ 0) :
    speakerOf α L w {u} ≠ 0 := by
  rw [speakerOf_apply_singleton, ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨weight_rpow_ne_zero hα h,
    ENNReal.sum_ne_top.mpr fun u' _ => weight_rpow_ne_top hα (hle u')⟩

/-! ### Choice scenarios

The bundled theory object: a choice space with an extension and an
observable form for each choice. Rationality and prior are arguments of the
derived kernels, not data — findings quantify over `α`. [franke-bergen-2020]'s
vanilla, LI, and GI models are three instantiations (identity observation
with the bare parse; `Prod.fst` over pair choices, eqs. 18/21); LU places its
latent in the state instead and is *not* a `Scenario` — its speaker
normalizes per lexicon, not against the pooled choice space. -/

variable (T C O : Type*) in
/-- A finite RSA choice scenario: each choice (an utterance, or an
(utterance, parse) pair) carries an extension and an observable form. -/
structure Scenario where
  /-- The extension of each choice. -/
  sem : C → Finset T
  /-- The observable form of each choice: what the listener hears. -/
  obs : C → O

namespace Scenario

section

variable {T C O : Type*} [MeasurableSpace T] [DecidableEq T] [MeasurableSingletonClass T]
  [MeasurableSpace C] [Fintype C] [DiscreteMeasurableSpace C]
  (s : Scenario T C O)

/-- The literal listener ([franke-bergen-2020] eq. 5 at the paper's standing
uniform prior): uniform over the choice's extension. -/
noncomputable def L0 : Kernel C T :=
  Kernel.ofFunOfCountable fun c => uniformOn ↑(s.sem c)

theorem L0_apply_singleton (c : C) (t : T) :
    s.L0 c {t} = if t ∈ s.sem c then ((s.sem c).card : ℝ≥0∞)⁻¹ else 0 := by
  show uniformOn ↑(s.sem c) {t} = _
  rw [uniformOn, cond_apply (s.sem c).measurableSet, Measure.count_apply_finset]
  split
  · rw [show ↑(s.sem c) ∩ {t} = ({t} : Set T) from
        Set.inter_eq_self_of_subset_right (by simpa using ‹t ∈ s.sem c›),
      Measure.count_singleton, mul_one]
  · rw [show ↑(s.sem c) ∩ {t} = (∅ : Set T) from by
        simpa [Set.eq_empty_iff_forall_notMem] using ‹t ∉ s.sem c›,
      measure_empty, mul_zero]

theorem L0_apply_singleton_le_one (c : C) (t : T) : s.L0 c {t} ≤ 1 := by
  rw [L0_apply_singleton]
  split
  · exact ENNReal.inv_le_one.mpr (by exact_mod_cast Finset.card_pos.mpr ⟨t, ‹_›⟩)
  · exact zero_le_one

theorem L0_apply_singleton_ne_zero {c : C} {t : T} (h : t ∈ s.sem c) :
    s.L0 c {t} ≠ 0 := by
  rw [L0_apply_singleton, if_pos h]
  simp

variable [Fintype T]

/-- The pragmatic speaker ([franke-bergen-2020] eqs. 6–7, 18a, 21a): best
response at rationality `α`. -/
noncomputable def speaker (α : ℝ) : Kernel T C := speakerOf α s.L0

instance (α : ℝ) : IsFiniteKernel (s.speaker α) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

variable (T C O) in
/-- Every state has a true choice — the proviso making the speaker a
probability kernel. -/
class Expressible (s : Scenario T C O) : Prop where
  exists_mem_sem : ∀ t, ∃ c, t ∈ s.sem c

theorem isMarkovKernel_speaker {α : ℝ} (hα : 0 ≤ α) [s.Expressible] :
    IsMarkovKernel (s.speaker α) :=
  isMarkovKernel_speakerOf hα s.L0 (fun c t => s.L0_apply_singleton_le_one c t)
    fun t => (Expressible.exists_mem_sem (s := s) t).imp
      fun _ h => s.L0_apply_singleton_ne_zero h

theorem speaker_apply_singleton_eq_zero {α : ℝ} (hα : 0 < α) {t : T} {c : C}
    (h : t ∉ s.sem c) : s.speaker α t {c} = 0 :=
  speakerOf_apply_singleton_eq_zero hα (by rw [s.L0_apply_singleton, if_neg h])

theorem speaker_apply_singleton_ne_zero {α : ℝ} (hα : 0 ≤ α) {t : T} {c : C}
    (h : t ∈ s.sem c) : s.speaker α t {c} ≠ 0 :=
  speakerOf_apply_singleton_ne_zero hα (fun c' => s.L0_apply_singleton_le_one c' t)
    (s.L0_apply_singleton_ne_zero h)

theorem speaker_real_singleton_eq_zero {α : ℝ} (hα : 0 < α) {t : T} {c : C}
    (h : t ∉ s.sem c) : (s.speaker α t).real {c} = 0 := by
  rw [measureReal_def, s.speaker_apply_singleton_eq_zero hα h, ENNReal.toReal_zero]

theorem speaker_real_singleton_pos {α : ℝ} (hα : 0 ≤ α) {t : T} {c : C}
    (h : t ∈ s.sem c) : 0 < (s.speaker α t).real {c} :=
  ENNReal.toReal_pos (s.speaker_apply_singleton_ne_zero hα h) (measure_ne_top _ _)

variable [MeasurableSpace O] [MeasurableSingletonClass O] [DecidableEq O]

omit [Fintype T] [DecidableEq T] [MeasurableSingletonClass T] [Fintype C]
  [MeasurableSingletonClass O] [DecidableEq O] in
private theorem measurable_obsPair : Measurable fun p : T × C => (s.obs p.2, p) :=
  (Measurable.of_discrete.comp measurable_snd).prodMk measurable_id

omit [DecidableEq T] [DecidableEq O] in
/-- A positive-prior state truly described by an `o`-shaped choice witnesses
a positive observation marginal. -/
theorem map_obs_comp_ne_zero {α : ℝ} {μ : Measure T} {t : T} {c : C} {o : O}
    (hμ : μ {t} ≠ 0) (hc : s.obs c = o) (hs : s.speaker α t {c} ≠ 0) :
    ((s.speaker α ∘ₘ μ).map s.obs) {o} ≠ 0 := by
  rw [Measure.map_apply Measurable.of_discrete (.singleton o)]
  intro h
  exact comp_apply_singleton_ne_zero _ _ hμ hs
    (measure_mono_null (Set.singleton_subset_iff.mpr (by simp [hc])) h)

section Listener

variable [StandardBorelSpace T] [Nonempty T] [StandardBorelSpace C] [Nonempty C]
  (α : ℝ) (μ : Measure T) [IsFiniteMeasure μ]

/-- Utterance production ([franke-bergen-2020] eq. 19a): the observable form
of the speaker's choice. -/
noncomputable def production (α : ℝ) : Kernel T O := (s.speaker α).map s.obs

/-- The joint distribution of the heard form with the (state, choice) pair. -/
noncomputable def jointObs : Measure (O × (T × C)) :=
  (μ ⊗ₘ s.speaker α).map fun p => (s.obs p.2, p)

instance : IsFiniteMeasure (s.jointObs α μ) :=
  inferInstanceAs (IsFiniteMeasure (Measure.map _ _))

omit [DecidableEq T] [MeasurableSingletonClass O] [DecidableEq O] [StandardBorelSpace T]
  [Nonempty T] [StandardBorelSpace C] [Nonempty C] [IsFiniteMeasure μ] in
/-- The heard form is distributed as the production marginal. -/
theorem jointObs_fst : (s.jointObs α μ).fst = (s.speaker α ∘ₘ μ).map s.obs := by
  rw [jointObs, Measure.fst, Measure.map_map measurable_fst s.measurable_obsPair,
    show (Prod.fst ∘ fun p : T × C => (s.obs p.2, p)) = s.obs ∘ Prod.snd from rfl,
    ← Measure.map_map Measurable.of_discrete measurable_snd, ← Measure.snd,
    Measure.snd_compProd]

/-- The joint pragmatic listener ([franke-bergen-2020] eqs. 18b/21b):
posterior over (state, choice) given the heard form. -/
noncomputable def jointListener : Kernel O (T × C) := (s.jointObs α μ).condKernel

/-- The state posterior ([franke-bergen-2020] eqs. 9/19b): the world marginal
of the joint listener. -/
noncomputable def listener : Kernel O T := (s.jointListener α μ).fst

/-- The choice posterior ([franke-bergen-2020] eq. 22, at pairs). -/
noncomputable def choicePosterior : Kernel O C := (s.jointListener α μ).snd

variable {α μ}

omit [DecidableEq T] in
/-- Exact Bayes for the joint listener at a positive-mass observation. -/
theorem jointListener_apply_singleton {o : O}
    (ho : ((s.speaker α ∘ₘ μ).map s.obs) {o} ≠ 0) (t : T) (c : C) :
    s.jointListener α μ o {(t, c)}
      = (if s.obs c = o then μ {t} * s.speaker α t {c} else 0)
        / ((s.speaker α ∘ₘ μ).map s.obs) {o} := by
  have hd := congrArg (fun m => m ({o} ×ˢ {(t, c)}))
    ((s.jointObs α μ).disintegrate (s.jointObs α μ).condKernel)
  beta_reduce at hd
  rw [Measure.compProd_apply_prod (.singleton o) (.singleton (t, c)),
    lintegral_singleton, s.jointObs_fst] at hd
  unfold jointObs at hd
  rw [Measure.map_apply s.measurable_obsPair
      ((MeasurableSet.singleton o).prod (.singleton (t, c)))] at hd
  by_cases hc : s.obs c = o
  · rw [show (fun p : T × C => (s.obs p.2, p)) ⁻¹' ({o} ×ˢ {(t, c)}) = {t} ×ˢ {c} from by
        ext ⟨t', c'⟩
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Prod.ext_iff]
        constructor
        · rintro ⟨_, h1, h2⟩
          exact ⟨h1, h2⟩
        · rintro ⟨rfl, rfl⟩
          exact ⟨hc, rfl, rfl⟩,
      Measure.compProd_apply_prod (.singleton t) (.singleton c), lintegral_singleton] at hd
    rw [jointListener, if_pos hc, ENNReal.eq_div_iff ho (measure_ne_top _ _), mul_comm]
    unfold jointObs
    rw [hd, mul_comm]
  · rw [show (fun p : T × C => (s.obs p.2, p)) ⁻¹' ({o} ×ˢ {(t, c)}) = (∅ : Set (T × C)) from by
        ext ⟨t', c'⟩
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Prod.ext_iff,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨h, -, rfl⟩
        exact hc h,
      measure_empty] at hd
    rw [jointListener, if_neg hc, ENNReal.zero_div]
    unfold jointObs
    exact (mul_eq_zero.mp hd).resolve_right ho

omit [DecidableEq T] in
/-- Listener preference on reals: the observation's marginal cancels, leaving
prior-weighted speaker mass pooled over the observation's fiber. -/
theorem listener_real_lt_iff {o : O}
    (ho : ((s.speaker α ∘ₘ μ).map s.obs) {o} ≠ 0) (t₁ t₂ : T) :
    (s.listener α μ o).real {t₁} < (s.listener α μ o).real {t₂}
      ↔ (∑ c ∈ Finset.univ.filter (s.obs · = o), μ.real {t₁} * (s.speaker α t₁).real {c})
        < ∑ c ∈ Finset.univ.filter (s.obs · = o), μ.real {t₂} * (s.speaker α t₂).real {c} := by
  have key : ∀ t : T, s.listener α μ o {t}
      = (∑ c ∈ Finset.univ.filter (s.obs · = o), μ {t} * s.speaker α t {c})
        / ((s.speaker α ∘ₘ μ).map s.obs) {o} := fun t => by
    rw [listener, Kernel.fst_apply, ← Measure.fst, Measure.fst_apply_singleton]
    simp_rw [s.jointListener_apply_singleton ho, div_eq_mul_inv, ← Finset.sum_mul,
      ← Finset.sum_filter]
  have hne : ∀ t : T,
      (∑ c ∈ Finset.univ.filter (s.obs · = o), μ {t} * s.speaker α t {c}) ≠ ∞ :=
    fun t => ENNReal.sum_ne_top.mpr fun c _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, key, key,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne t₁) ho) (ENNReal.div_ne_top (hne t₂) ho),
    ENNReal.div_lt_div_iff_left ho (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne t₁) (hne t₂),
    ENNReal.toReal_sum (fun c _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun c _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

/-- Support preference: hearing `o`, the listener strictly prefers a state
where some `o`-shaped choice is true over one where none is. The witness at
`t₂` also carries the positive observation marginal — no side conditions. -/
theorem listener_real_lt_of_support {α : ℝ} (hα : 0 < α) {μ : Measure T}
    [IsFiniteMeasure μ] {o : O} {t₁ t₂ : T} (hμ : μ {t₂} ≠ 0)
    (h₁ : ∀ c, s.obs c = o → t₁ ∉ s.sem c) (h₂ : ∃ c, s.obs c = o ∧ t₂ ∈ s.sem c) :
    (s.listener α μ o).real {t₁} < (s.listener α μ o).real {t₂} := by
  obtain ⟨c₂, hc₂, hmem⟩ := h₂
  rw [s.listener_real_lt_iff
      (s.map_obs_comp_ne_zero hμ hc₂ (s.speaker_apply_singleton_ne_zero hα.le hmem)),
    Finset.sum_congr rfl fun c hc => by
      rw [s.speaker_real_singleton_eq_zero hα (h₁ c (Finset.mem_filter.mp hc).2), mul_zero],
    Finset.sum_const_zero]
  exact Finset.sum_pos' (fun c _ => mul_nonneg measureReal_nonneg measureReal_nonneg)
    ⟨c₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc₂⟩,
      mul_pos (ENNReal.toReal_pos hμ (measure_ne_top _ _))
        (s.speaker_real_singleton_pos hα.le hmem)⟩

end Listener

end

end Scenario

end RSA

