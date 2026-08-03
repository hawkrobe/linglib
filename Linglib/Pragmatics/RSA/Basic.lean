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
prior-weighted speaker masses; the observation's marginal cancels. -/
theorem posterior_real_singleton_lt_iff {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0)
    (ω₁ ω₂ : Ω) :
    ((κ†μ) x).real {ω₁} < ((κ†μ) x).real {ω₂}
      ↔ μ {ω₁} * κ ω₁ {x} < μ {ω₂} * κ ω₂ {x} := by
  rw [measureReal_def, measureReal_def, posterior_apply_singleton κ μ hx,
    posterior_apply_singleton κ μ hx,
    ENNReal.toReal_lt_toReal
      (ENNReal.div_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) hx)
      (ENNReal.div_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) hx),
    ENNReal.div_lt_div_iff_left hx (measure_ne_top _ _)]

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

/-! ### Posteriors from partially observed emissions

For a kernel emitting a pair of which only the first component is observed —
RSA's intention models, where the speaker chooses an (utterance, parse) pair
and the listener hears only the utterance — the posterior over parameter and
unobserved component is the conditional kernel of the reassociated joint:
the same construction as `ProbabilityTheory.posterior` with a reassociation
in place of the swap. -/

namespace ProbabilityTheory

variable {Ω 𝓧 Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧] [MeasurableSpace Θ]
  [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Θ] [Nonempty Θ]
  (κ : Kernel Ω (𝓧 × Θ)) (μ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteKernel κ]

omit [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Θ] [Nonempty Θ] in
lemma measurable_emissionReassoc :
    Measurable fun p : Ω × (𝓧 × Θ) => (p.2.1, (p.1, p.2.2)) :=
  (measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

/-- The joint distribution of observed component and (parameter, unobserved
component). -/
noncomputable def emissionJoint : Measure (𝓧 × (Ω × Θ)) :=
  (μ ⊗ₘ κ).map fun p => (p.2.1, (p.1, p.2.2))

instance : IsFiniteMeasure (emissionJoint κ μ) :=
  inferInstanceAs (IsFiniteMeasure ((μ ⊗ₘ κ).map _))

omit [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Θ] [Nonempty Θ] in
/-- The observed component of the joint is distributed as the data marginal. -/
theorem emissionJoint_fst : (emissionJoint κ μ).fst = ((κ ∘ₘ μ).map Prod.fst) := by
  rw [emissionJoint, Measure.fst,
    Measure.map_map measurable_fst measurable_emissionReassoc,
    show (Prod.fst ∘ fun p : Ω × (𝓧 × Θ) => (p.2.1, (p.1, p.2.2)))
      = Prod.fst ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_fst measurable_snd, ← Measure.snd,
    Measure.snd_compProd]

/-- Posterior over parameter and unobserved emission component, given the
observed first component of a jointly emitted pair. -/
noncomputable def emissionPosterior : Kernel 𝓧 (Ω × Θ) :=
  (emissionJoint κ μ).condKernel

instance : IsMarkovKernel (emissionPosterior κ μ) :=
  inferInstanceAs (IsMarkovKernel (emissionJoint κ μ).condKernel)

variable [MeasurableSingletonClass Ω] [MeasurableSingletonClass 𝓧]
  [MeasurableSingletonClass Θ]

/-- Exact Bayes for the emission posterior at a positive-mass observation. -/
theorem emissionPosterior_apply_singleton {x : 𝓧}
    (hx : ((κ ∘ₘ μ).map Prod.fst) {x} ≠ 0) (ω : Ω) (θ : Θ) :
    emissionPosterior κ μ x {(ω, θ)}
      = μ {ω} * κ ω {(x, θ)} / ((κ ∘ₘ μ).map Prod.fst) {x} := by
  have hd := congrArg (fun m => m ({x} ×ˢ {(ω, θ)}))
    ((emissionJoint κ μ).disintegrate (emissionJoint κ μ).condKernel)
  beta_reduce at hd
  rw [Measure.compProd_apply_prod (.singleton x) (.singleton (ω, θ)),
    lintegral_singleton, emissionJoint_fst] at hd
  unfold emissionJoint at hd
  rw [Measure.map_apply measurable_emissionReassoc
      ((MeasurableSet.singleton x).prod (.singleton (ω, θ))),
    show (fun p : Ω × (𝓧 × Θ) => (p.2.1, (p.1, p.2.2))) ⁻¹' ({x} ×ˢ {(ω, θ)})
        = {ω} ×ˢ {(x, θ)} from by
      ext ⟨a, b, c⟩
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Prod.ext_iff]
      tauto,
    Measure.compProd_apply_prod (.singleton ω) (.singleton (x, θ)),
    lintegral_singleton] at hd
  rw [emissionPosterior, ENNReal.eq_div_iff hx (measure_ne_top _ _), mul_comm]
  unfold emissionJoint
  rw [hd]
  ring

/-- Parameter preference under the emission posterior, on reals: the
observation's marginal cancels, leaving prior-weighted pooled emissions. -/
theorem emissionPosterior_fst_real_lt_iff [Fintype Θ] {x : 𝓧}
    (hx : ((κ ∘ₘ μ).map Prod.fst) {x} ≠ 0) (ω₁ ω₂ : Ω) :
    (emissionPosterior κ μ x).fst.real {ω₁} < (emissionPosterior κ μ x).fst.real {ω₂}
      ↔ (∑ θ, μ {ω₁} * κ ω₁ {(x, θ)}) < ∑ θ, μ {ω₂} * κ ω₂ {(x, θ)} := by
  have hne : ∀ ω, (∑ θ, μ {ω} * κ ω {(x, θ)}) ≠ ∞ := fun ω =>
    ENNReal.sum_ne_top.mpr fun θ _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, Measure.fst_apply_singleton,
    Measure.fst_apply_singleton]
  simp_rw [emissionPosterior_apply_singleton κ μ hx, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne ω₁) hx) (ENNReal.div_ne_top (hne ω₂) hx),
    ENNReal.div_lt_div_iff_left hx (measure_ne_top _ _)]

/-- Unobserved-component preference under the emission posterior, on reals. -/
theorem emissionPosterior_snd_real_lt_iff [Fintype Ω] {x : 𝓧}
    (hx : ((κ ∘ₘ μ).map Prod.fst) {x} ≠ 0) (θ₁ θ₂ : Θ) :
    (emissionPosterior κ μ x).snd.real {θ₁} < (emissionPosterior κ μ x).snd.real {θ₂}
      ↔ (∑ ω, μ {ω} * κ ω {(x, θ₁)}) < ∑ ω, μ {ω} * κ ω {(x, θ₂)} := by
  have hne : ∀ θ, (∑ ω, μ {ω} * κ ω {(x, θ)}) ≠ ∞ := fun θ =>
    ENNReal.sum_ne_top.mpr fun ω _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, Measure.snd_apply_singleton,
    Measure.snd_apply_singleton]
  simp_rw [emissionPosterior_apply_singleton κ μ hx, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne θ₁) hx) (ENNReal.div_ne_top (hne θ₂) hx),
    ENNReal.div_lt_div_iff_left hx (measure_ne_top _ _)]

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

/-- Speaker preference on reals is utility comparison (eq. 2's softmax is
strictly monotone; the partition function cancels). -/
theorem speaker_real_singleton_lt_iff {α : ℝ} {util : W → U → EReal} (w : W)
    (h0 : (∑ u, ((α : EReal) * util w u).exp) ≠ 0)
    (hZtop : (∑ u, ((α : EReal) * util w u).exp) ≠ ∞) (u₁ u₂ : U) :
    (speaker α util w).real {u₁} < (speaker α util w).real {u₂}
      ↔ (α : EReal) * util w u₁ < (α : EReal) * util w u₂ := by
  rw [speaker, Kernel.ofWeights_real_singleton_lt_iff w h0 hZtop, EReal.exp_lt_exp_iff]

end RSA
