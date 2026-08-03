import Mathlib.Probability.Kernel.Posterior
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Linglib.Pragmatics.RSA.Dominates

/-!
# The Rational Speech Act pipeline on probability kernels

The RSA model ([frank-goodman-2012]; [degen-2023] eqs. 1–4;
[franke-bergen-2020] eqs. 5–22) in mathlib's probability vocabulary. A
`RSA.Scenario` bundles a choice space with an extension and an observable
form per choice; the literal listener is uniform on the extension, the
speaker is the best response in power-weight form (`ENNReal.rpow` is total,
so falsity needs no signed utilities), and the listeners are conditionals of
the joint — rationality and priors are arguments, so findings quantify over
them. Preference facts come in two registers, each closed by `decide`:
`Multiset.StrictDominates` certificates on informativity profiles (strict
stochastic dominance — uniform in the rationality, with empty fibers as the
support case), and pinned natural rationality, where comparisons clear to ℕ
inequalities via `Multiset.divPowSum`.

## Main definitions

* `RSA.literalListener` — eq. 1: a prior conditioned on the extension.
* `RSA.speakerOf` — eqs. 2/6–7: the best-response speaker to a listener
  kernel, as `ProbabilityTheory.Kernel.ofWeights` of `L ^ α`.
* `RSA.Scenario` — the bundled model: `sem`, `obs`, and the derived `L0`,
  `speaker`, `production`, `jointListener`, `listener`, `choicePosterior`.
* `RSA.Scenario.pool` — choice-side latents: the speaker chooses the family
  index, normalizing across the pooled pairs (eqs. 18a/21a).
* `RSA.Scenario.familySpeaker`, `RSA.Scenario.familyListener` — state-side
  latents: the index is a speaker argument, normalization is per-index
  (eqs. 11–13). `pool_L0` shows the two architectures share their weights —
  they differ only in the position of the latent.

## Main statements

* `ProbabilityTheory.posterior_apply_singleton` — exact Bayes for `κ†μ` at a
  positive-mass observation.
* `RSA.Scenario.listener_real_lt_of_prodMul_strictDominates` — the
  certificate register: strict domination of fiber-by-rest profile products
  decides listener preference uniformly in the rationality.
* `RSA.Scenario.listener_real_lt_of_divPowSum`,
  `RSA.Scenario.choicePosterior_real_lt_of_divPowSum` — the evaluation
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

/-- Pool a family of scenarios into one whose choices carry the family index:
the speaker *chooses* the index with the utterance, normalizing across the
whole family ([franke-bergen-2020] eqs. 18a/21a). `familySpeaker` instead
keeps the index as an argument of the speaker (eq. 11) — with `pool_L0`, the
paper's observation (p. e86) that the two architectures differ only in the
position of the latent parameter. -/
@[simps] def pool {T C O L : Type*} (f : L → Scenario T C O) : Scenario T (C × L) O where
  sem cl := (f cl.2).sem cl.1
  obs cl := (f cl.2).obs cl.1

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

omit [DecidableEq T] [MeasurableSingletonClass T] in
/-- Pooling does not change the literal listener: `pool` and `familySpeaker`
share their weights and differ only in the normalization domain — the
type-level content of [franke-bergen-2020]'s contrast between eq. 11 and
eqs. 18a/21a (p. e86). -/
theorem pool_L0 {L : Type*} [Fintype L] [MeasurableSpace L] [DiscreteMeasurableSpace L]
    (f : L → Scenario T C O) (c : C) (l : L) :
    (pool f).L0 (c, l) = (f l).L0 c := rfl

variable [Fintype T]

/-- The pragmatic speaker ([franke-bergen-2020] eqs. 6–7, 18a, 21a): best
response at rationality `α`. -/
noncomputable def speaker (α : ℝ) : Kernel T C := speakerOf α s.L0

instance (α : ℝ) : IsFiniteKernel (s.speaker α) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

omit [DecidableEq T] in
theorem speaker_apply_univ_le_one (α : ℝ) (t : T) : s.speaker α t Set.univ ≤ 1 :=
  Kernel.ofWeights_apply_univ_le_one (fun w u => s.L0 u {w} ^ α) t

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

/-! #### Informativity profiles

The combinatorial shadow of the model: the multiset of extension sizes of a
state's true choices. Softmax masses are ratios of `Multiset.invPowSum`s over
profiles, so preference certificates are `Multiset.StrictDominates` facts
closed by `decide` — uniform in the rationality. -/

variable [DecidableEq O]

/-- The choices true at a state. -/
def trueChoices (t : T) : Finset C := Finset.univ.filter (t ∈ s.sem ·)

/-- The informativity profile: extension sizes of the true choices. -/
def profile (t : T) : Multiset ℕ := (s.trueChoices t).val.map fun c => (s.sem c).card

/-- The profile restricted to choices heard as `o`. -/
def fiberProfile (o : O) (t : T) : Multiset ℕ :=
  ((s.trueChoices t).filter (s.obs · = o)).val.map fun c => (s.sem c).card

/-- The profile of true choices heard otherwise. -/
def restProfile (o : O) (t : T) : Multiset ℕ :=
  ((s.trueChoices t).filter (s.obs · ≠ o)).val.map fun c => (s.sem c).card

omit [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] [Fintype T] in
theorem profile_eq_fiberProfile_add_restProfile (o : O) (t : T) :
    s.profile t = s.fiberProfile o t + s.restProfile o t := by
  rw [fiberProfile, restProfile, ← Multiset.map_add, profile]
  congr 1
  rw [Finset.filter_val, Finset.filter_val, Multiset.filter_add_not]

omit [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] [Fintype T] [DecidableEq O] in
theorem zero_notMem_profile (t : T) : 0 ∉ s.profile t := by
  simp only [profile, Multiset.mem_map, not_exists, not_and]
  intro c hc hcard
  rw [Finset.mem_val, trueChoices, Finset.mem_filter] at hc
  exact Finset.card_ne_zero_of_mem hc.2 hcard

omit [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] [Fintype T] in
theorem zero_notMem_fiberProfile (o : O) (t : T) : 0 ∉ s.fiberProfile o t := fun h =>
  s.zero_notMem_profile t
    (s.profile_eq_fiberProfile_add_restProfile o t ▸ Multiset.mem_add.mpr (Or.inl h))

omit [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] [Fintype T] in
theorem zero_notMem_restProfile (o : O) (t : T) : 0 ∉ s.restProfile o t := fun h =>
  s.zero_notMem_profile t
    (s.profile_eq_fiberProfile_add_restProfile o t ▸ Multiset.mem_add.mpr (Or.inr h))

omit [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] [Fintype T] in
/-- A nonempty fiber profile exhibits an `o`-shaped true choice — certificates
carry their own truth witnesses. -/
theorem exists_of_fiberProfile_ne_zero {o : O} {t : T} (h : s.fiberProfile o t ≠ 0) :
    ∃ c, s.obs c = o ∧ t ∈ s.sem c := by
  rw [fiberProfile, ne_eq, Multiset.map_eq_zero, Finset.val_eq_zero, ← ne_eq,
    ← Finset.nonempty_iff_ne_empty] at h
  obtain ⟨c, hc⟩ := h
  rw [Finset.mem_filter, trueChoices, Finset.mem_filter] at hc
  exact ⟨c, hc.2, hc.1.2⟩

omit [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] [Fintype T] [DecidableEq O] in
theorem profile_ne_zero [s.Expressible] (t : T) : s.profile t ≠ 0 := by
  obtain ⟨c, hc⟩ := Expressible.exists_mem_sem (s := s) t
  intro h
  rw [profile, Multiset.map_eq_zero, Finset.val_eq_zero] at h
  exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)
    (h ▸ Finset.notMem_empty c)

omit [Fintype T] [DecidableEq O] in
theorem sum_rpow_L0 {α : ℝ} (hα : 0 < α) (t : T) :
    ∑ c, s.L0 c {t} ^ α = (s.profile t).invPowSum α := by
  simp_rw [L0_apply_singleton, apply_ite (· ^ α), ENNReal.zero_rpow_of_pos hα,
    ← Finset.sum_filter]
  rw [profile, Multiset.invPowSum, Multiset.map_map]
  rfl

omit [Fintype T] in
theorem sum_fiber_rpow_L0 {α : ℝ} (hα : 0 < α) (o : O) (t : T) :
    ∑ c ∈ Finset.univ.filter (s.obs · = o), s.L0 c {t} ^ α
      = (s.fiberProfile o t).invPowSum α := by
  simp_rw [L0_apply_singleton, apply_ite (· ^ α), ENNReal.zero_rpow_of_pos hα,
    ← Finset.sum_filter]
  rw [fiberProfile, Multiset.invPowSum, Multiset.map_map,
    show (Finset.univ.filter (s.obs · = o)).filter (fun c => t ∈ s.sem c)
      = (s.trueChoices t).filter (s.obs · = o) from by
    rw [trueChoices, Finset.filter_comm]]
  rfl

/-- Pooled speaker mass over an observation's fiber is a ratio of profile
sums — [franke-bergen-2020] eq. 8, structurally. -/
theorem sum_fiber_speaker {α : ℝ} (hα : 0 < α) (o : O) (t : T) :
    ∑ c ∈ Finset.univ.filter (s.obs · = o), s.speaker α t {c}
      = (s.fiberProfile o t).invPowSum α / (s.profile t).invPowSum α := by
  simp_rw [speaker, speakerOf_apply_singleton, div_eq_mul_inv, ← Finset.sum_mul]
  rw [s.sum_fiber_rpow_L0 hα, s.sum_rpow_L0 hα, ← div_eq_mul_inv]

omit [DecidableEq O] in
/-- Exact speaker mass on reals: extension-size weight over the state's
partition. -/
theorem speaker_real_singleton {α : ℝ} (hα : 0 < α) (t : T) (c : C) :
    (s.speaker α t).real {c}
      = (if t ∈ s.sem c then (((s.sem c).card : ℝ))⁻¹ ^ α else 0)
        / ((s.profile t).invPowSum α).toReal := by
  rw [measureReal_def, speaker, speakerOf_apply_singleton, s.sum_rpow_L0 hα,
    ENNReal.toReal_div, L0_apply_singleton, apply_ite (· ^ α),
    ENNReal.zero_rpow_of_pos hα, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast]

omit [DecidableEq O] in
theorem speaker_real_singleton_eq_zero {α : ℝ} (hα : 0 < α) {t : T} {c : C}
    (h : t ∉ s.sem c) : (s.speaker α t).real {c} = 0 := by
  rw [measureReal_def, s.speaker_apply_singleton_eq_zero hα h, ENNReal.toReal_zero]

omit [DecidableEq T] [DecidableEq O] in
/-- Speaker shares over any set of choices stay within the row's unit mass. -/
theorem sum_speaker_real_singleton_le_one (α : ℝ) (t : T) (S : Finset C) :
    ∑ c ∈ S, (s.speaker α t).real {c} ≤ 1 := by
  have hle : s.speaker α t ↑S ≤ 1 :=
    le_trans (measure_mono (Set.subset_univ _)) (s.speaker_apply_univ_le_one α t)
  calc ∑ c ∈ S, (s.speaker α t).real {c}
      = (s.speaker α t).real ↑S := by
        simp_rw [measureReal_def, ← ENNReal.toReal_sum fun c _ => measure_ne_top _ _,
          sum_measure_singleton]
    _ ≤ 1 := by
        rw [measureReal_def, ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono ENNReal.one_ne_top hle

omit [DecidableEq O] in
/-- Competition: any other true choice caps a share strictly below one. -/
theorem speaker_real_singleton_lt_one [DecidableEq C] {α : ℝ} (hα : 0 ≤ α) {t : T}
    {c c' : C} (hne : c' ≠ c) (hmem' : t ∈ s.sem c') : (s.speaker α t).real {c} < 1 := by
  have hsum := s.sum_speaker_real_singleton_le_one α t {c, c'}
  rw [Finset.sum_insert (by simpa using fun h => hne h.symm), Finset.sum_singleton] at hsum
  have hpos : 0 < (s.speaker α t).real {c'} :=
    ENNReal.toReal_pos (s.speaker_apply_singleton_ne_zero hα hmem') (measure_ne_top _ _)
  linarith

omit [DecidableEq O] in
/-- Informativity monotonicity ([franke-bergen-2020] eq. 7's qualitative
claim): between two true choices, the one with the strictly smaller extension
is produced with strictly higher probability, at every positive
rationality. -/
theorem speaker_real_singleton_lt_of_card_lt {α : ℝ} (hα : 0 < α) {t : T} {c c' : C}
    (hmem : t ∈ s.sem c) (hmem' : t ∈ s.sem c')
    (hcard : (s.sem c').card < (s.sem c).card) :
    (s.speaker α t).real {c} < (s.speaker α t).real {c'} := by
  have hterm : s.L0 c {t} ^ α ≠ 0 :=
    weight_rpow_ne_zero hα.le (s.L0_apply_singleton_ne_zero hmem)
  have hZ0 : (∑ u, s.L0 u {t} ^ α) ≠ 0 := fun h =>
    hterm (le_antisymm (le_trans
      (Finset.single_le_sum (f := fun u => s.L0 u {t} ^ α) (fun u _ => zero_le)
        (Finset.mem_univ c)) h.le) zero_le)
  rw [speaker, speakerOf, Kernel.ofWeights_real_singleton_lt_iff t hZ0
      (ENNReal.sum_ne_top.mpr fun u _ =>
        weight_rpow_ne_top hα.le (s.L0_apply_singleton_le_one u t)),
    s.L0_apply_singleton, s.L0_apply_singleton, if_pos hmem, if_pos hmem']
  exact ENNReal.rpow_lt_rpow
    (ENNReal.inv_lt_inv.2 (by exact_mod_cast hcard)) hα

omit [DecidableEq O] in
/-- Softmax constant-utility invariance: when every true choice at a state
has the same extension size, the speaker is uniform on them — each share is
`m⁻¹` regardless of the rationality. -/
theorem speaker_real_singleton_of_profile_replicate {α : ℝ} (hα : 0 < α) {t : T} {c : C}
    {m n : ℕ} (hprof : s.profile t = Multiset.replicate m n) (hmem : t ∈ s.sem c) :
    (s.speaker α t).real {c} = (m : ℝ)⁻¹ := by
  have hcmem : (s.sem c).card ∈ s.profile t :=
    Multiset.mem_map_of_mem _ (by
      rw [Finset.mem_val, trueChoices, Finset.mem_filter]
      exact ⟨Finset.mem_univ c, hmem⟩)
  have hn : (s.sem c).card = n := Multiset.eq_of_mem_replicate (hprof ▸ hcmem)
  have hn0 : n ≠ 0 := hn ▸ Finset.card_ne_zero_of_mem hmem
  have hx : (0 : ℝ) < ((n : ℝ))⁻¹ ^ α :=
    Real.rpow_pos_of_pos (by positivity) α
  rw [s.speaker_real_singleton hα, if_pos hmem, hprof, hn,
    show ((Multiset.replicate m n).invPowSum α).toReal = m * ((n : ℝ))⁻¹ ^ α by
      rw [Multiset.invPowSum_replicate, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast],
    div_mul_eq_div_div_swap, div_self hx.ne', one_div]

omit [DecidableEq O] in
/-- Exact speaker mass at a natural rationality, as a ratio of ℕ-valued
common-denominator sums. -/
theorem speaker_real_singleton_divPowSum {k D : ℕ} (hk : k ≠ 0) (hD : D ≠ 0) {t : T}
    (hdvd : ∀ n ∈ s.profile t, n ∣ D) (c : C) :
    (s.speaker k t).real {c}
      = (if t ∈ s.sem c then (((D / (s.sem c).card) ^ k : ℕ) : ℝ) else 0)
        / ((s.profile t).divPowSum D k : ℝ) := by
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hDk : ((D : ℝ) ^ k) ≠ 0 := pow_ne_zero k (Nat.cast_ne_zero.mpr hD)
  rw [s.speaker_real_singleton hα, Multiset.invPowSum_toReal_eq hD k hdvd]
  split
  · have hcard : (s.sem c).card ∣ D := hdvd _ (Multiset.mem_map_of_mem _ (by
      rw [Finset.mem_val, trueChoices, Finset.mem_filter]
      exact ⟨Finset.mem_univ c, ‹_›⟩))
    have hcard0 : ((s.sem c).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      fun h0 => hD (Nat.eq_zero_of_zero_dvd (h0 ▸ hcard))
    have hinv : (((s.sem c).card : ℝ))⁻¹ = ((D / (s.sem c).card : ℕ) : ℝ) / D := by
      rw [eq_div_iff (Nat.cast_ne_zero.mpr hD),
        show (D : ℝ) = ((D / (s.sem c).card : ℕ) : ℝ) * ((s.sem c).card : ℝ) by
          rw [← Nat.cast_mul, Nat.div_mul_cancel hcard],
        mul_comm _ ((s.sem c).card : ℝ), ← mul_assoc, inv_mul_cancel₀ hcard0, one_mul]
    rw [Real.rpow_natCast, hinv, div_pow, ← Nat.cast_pow, ← Nat.cast_pow,
      div_div_div_comm, div_self (Nat.cast_ne_zero.mpr (pow_ne_zero k hD) : ((D ^ k : ℕ) : ℝ) ≠ 0),
      div_one]
  · rw [zero_div, zero_div]

variable [MeasurableSpace O] [MeasurableSingletonClass O]

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

omit [DecidableEq T] in
/-- Choice preference among `o`-shaped choices reduces to comparing
prior-weighted speaker masses across states. -/
theorem choicePosterior_real_lt_iff {o : O}
    (ho : ((s.speaker α ∘ₘ μ).map s.obs) {o} ≠ 0) {c₁ c₂ : C}
    (h₁ : s.obs c₁ = o) (h₂ : s.obs c₂ = o) :
    (s.choicePosterior α μ o).real {c₁} < (s.choicePosterior α μ o).real {c₂}
      ↔ (∑ t, μ.real {t} * (s.speaker α t).real {c₁})
        < ∑ t, μ.real {t} * (s.speaker α t).real {c₂} := by
  have key : ∀ c, s.obs c = o → s.choicePosterior α μ o {c}
      = (∑ t, μ {t} * s.speaker α t {c}) / ((s.speaker α ∘ₘ μ).map s.obs) {o} :=
    fun c hc => by
      rw [choicePosterior, Kernel.snd_apply, ← Measure.snd, Measure.snd_apply_singleton]
      simp_rw [s.jointListener_apply_singleton ho, if_pos hc, div_eq_mul_inv,
        ← Finset.sum_mul]
  have hne : ∀ c : C, (∑ t, μ {t} * s.speaker α t {c}) ≠ ∞ := fun c =>
    ENNReal.sum_ne_top.mpr fun t _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, key c₁ h₁, key c₂ h₂,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne c₁) ho) (ENNReal.div_ne_top (hne c₂) ho),
    ENNReal.div_lt_div_iff_left ho (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne c₁) (hne c₂),
    ENNReal.toReal_sum (fun t _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun t _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

private theorem sum_div_lt_sum_div_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b z : ι → ℝ}
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

/-- The evaluation register for the choice posterior at a natural rationality
and equal priors: pooled preference between two `o`-shaped choices is the
ℕ-valued common-denominator comparison over all states — a kernel `decide`.
The strict inequality carries its own truth witness. -/
theorem choicePosterior_real_lt_of_divPowSum [s.Expressible] {k D : ℕ}
    (hk : k ≠ 0) (hD : D ≠ 0) (hdvd : ∀ t : T, ∀ n ∈ s.profile t, n ∣ D)
    (hμeq : ∀ t t' : T, μ {t} = μ {t'}) (hμ0 : ∀ t : T, μ {t} ≠ 0)
    {o : O} {c₁ c₂ : C} (h₁ : s.obs c₁ = o) (h₂ : s.obs c₂ = o)
    (hlt : (∑ t : T, if t ∈ s.sem c₁ then
        (D / (s.sem c₁).card) ^ k * ∏ t' ∈ Finset.univ.erase t, (s.profile t').divPowSum D k
      else 0)
      < ∑ t : T, if t ∈ s.sem c₂ then
        (D / (s.sem c₂).card) ^ k * ∏ t' ∈ Finset.univ.erase t, (s.profile t').divPowSum D k
      else 0) :
    (s.choicePosterior k μ o).real {c₁} < (s.choicePosterior k μ o).real {c₂} := by
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) hlt))
  have hmem₀ : t₀ ∈ s.sem c₂ := by
    by_contra h
    exact ht₀ (if_neg h)
  have ho : ((s.speaker k ∘ₘ μ).map s.obs) {o} ≠ 0 :=
    s.map_obs_comp_ne_zero (hμ0 t₀) h₂ (s.speaker_apply_singleton_ne_zero hα.le hmem₀)
  have hprior : ∀ c : C, (∑ t : T, μ.real {t} * (s.speaker k t).real {c})
      = μ.real {t₀} * ∑ t : T,
          (if t ∈ s.sem c then (((D / (s.sem c).card) ^ k : ℕ) : ℝ) else 0)
            / ((s.profile t).divPowSum D k : ℝ) := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show μ.real {t} = μ.real {t₀} from by
        rw [measureReal_def, measureReal_def, hμeq t t₀],
      s.speaker_real_singleton_divPowSum hk hD (hdvd t)]
  rw [s.choicePosterior_real_lt_iff ho h₁ h₂, hprior, hprior,
    mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real {t₀} from ENNReal.toReal_pos (hμ0 t₀) (measure_ne_top _ _)),
    sum_div_lt_sum_div_iff fun t => by
      exact_mod_cast Multiset.divPowSum_pos hD (hdvd t) (s.profile_ne_zero t)]
  simp only [ite_mul, zero_mul]
  exact_mod_cast hlt

/-- Listener preference at equal priors reduces to the cross-multiplied
profile comparison, on reals: the observation marginal and the shared prior
cancel. Both registers' closers enter here. -/
theorem listener_real_lt_iff_invPowSum [s.Expressible] {α : ℝ} (hα : 0 < α)
    {o : O} {t₁ t₂ : T} (hμeq : μ {t₁} = μ {t₂}) (hμ0 : μ {t₂} ≠ 0)
    (h₂ : ∃ c, s.obs c = o ∧ t₂ ∈ s.sem c) :
    ((s.listener α μ o).real {t₁} < (s.listener α μ o).real {t₂})
      ↔ ((s.fiberProfile o t₁).invPowSum α).toReal * ((s.profile t₂).invPowSum α).toReal
        < ((s.fiberProfile o t₂).invPowSum α).toReal * ((s.profile t₁).invPowSum α).toReal := by
  obtain ⟨c₂, hc₂, hmem⟩ := h₂
  have hWne : ∀ t, (s.fiberProfile o t).invPowSum α ≠ ∞ := fun t =>
    Multiset.invPowSum_ne_top hα.le (s.zero_notMem_fiberProfile o t)
  have hZ0 : ∀ t, (s.profile t).invPowSum α ≠ 0 := fun t =>
    (Multiset.invPowSum_pos hα.le (s.profile_ne_zero t)).ne'
  have hZne : ∀ t, (s.profile t).invPowSum α ≠ ∞ := fun t =>
    Multiset.invPowSum_ne_top hα.le (s.zero_notMem_profile t)
  have key : ∀ t : T,
      (∑ c ∈ Finset.univ.filter (s.obs · = o), μ.real {t} * (s.speaker α t).real {c})
        = (μ {t} * ((s.fiberProfile o t).invPowSum α / (s.profile t).invPowSum α)).toReal :=
    fun t => by
      rw [← Finset.mul_sum, measureReal_def,
        show (∑ c ∈ Finset.univ.filter (s.obs · = o), (s.speaker α t).real {c})
          = ((s.fiberProfile o t).invPowSum α / (s.profile t).invPowSum α).toReal from by
          rw [← s.sum_fiber_speaker hα, ENNReal.toReal_sum fun c _ => measure_ne_top _ _]
          simp_rw [measureReal_def],
        ENNReal.toReal_mul]
  rw [s.listener_real_lt_iff
      (s.map_obs_comp_ne_zero hμ0 hc₂ (s.speaker_apply_singleton_ne_zero hα.le hmem)),
    key, key, hμeq,
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

omit [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace C]
  [DiscreteMeasurableSpace C] [Fintype T] [MeasurableSpace O] [MeasurableSingletonClass O]
  [StandardBorelSpace T] [Nonempty T] [StandardBorelSpace C] [Nonempty C]
  [IsFiniteMeasure μ] in
/-- The certificate closes the odds comparison: strict domination of the
fiber-by-rest cross products decides it uniformly in the rationality (the
shared fiber-by-fiber terms cancel). -/
theorem invPowSum_odds_lt_of_prodMul_strictDominates {α : ℝ} (hα : 0 < α)
    {o : O} {t₁ t₂ : T}
    (hcert : ((s.fiberProfile o t₂).prodMul (s.restProfile o t₁)).StrictDominates
      ((s.fiberProfile o t₁).prodMul (s.restProfile o t₂))) :
    ((s.fiberProfile o t₁).invPowSum α).toReal * ((s.profile t₂).invPowSum α).toReal
      < ((s.fiberProfile o t₂).invPowSum α).toReal * ((s.profile t₁).invPowSum α).toReal := by
  have hWne : ∀ t, (s.fiberProfile o t).invPowSum α ≠ ∞ := fun t =>
    Multiset.invPowSum_ne_top hα.le (s.zero_notMem_fiberProfile o t)
  have hodds : (s.fiberProfile o t₁).invPowSum α * (s.restProfile o t₂).invPowSum α
      < (s.fiberProfile o t₂).invPowSum α * (s.restProfile o t₁).invPowSum α := by
    rw [← Multiset.invPowSum_prodMul hα.le, ← Multiset.invPowSum_prodMul hα.le]
    exact hcert.invPowSum_lt hα
      (Multiset.zero_notMem_prodMul (s.zero_notMem_fiberProfile o t₁)
        (s.zero_notMem_restProfile o t₂))
  rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul,
    ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (hWne t₁)
        (Multiset.invPowSum_ne_top hα.le (s.zero_notMem_profile t₂)))
      (ENNReal.mul_ne_top (hWne t₂)
        (Multiset.invPowSum_ne_top hα.le (s.zero_notMem_profile t₁))),
    s.profile_eq_fiberProfile_add_restProfile o t₁,
    s.profile_eq_fiberProfile_add_restProfile o t₂, Multiset.invPowSum_add,
    Multiset.invPowSum_add, mul_add, mul_add, mul_comm ((s.fiberProfile o t₂).invPowSum α)]
  exact ENNReal.add_lt_add_left
    (ENNReal.mul_ne_top (hWne t₁) (hWne t₂)) hodds

/-- The certificate register: at equal priors, strict domination of the
fiber-by-rest profile products decides listener preference uniformly in the
rationality. The certificate carries its own truth witness, so a finding is a
single decided `Multiset.StrictDominates` fact. An empty fiber at `t₁` is the
support case: any nonempty product strictly dominates `0`. -/
theorem listener_real_lt_of_prodMul_strictDominates [s.Expressible] {α : ℝ} (hα : 0 < α)
    {o : O} {t₁ t₂ : T} (hμeq : μ {t₁} = μ {t₂}) (hμ0 : μ {t₂} ≠ 0)
    (hcert : ((s.fiberProfile o t₂).prodMul (s.restProfile o t₁)).StrictDominates
      ((s.fiberProfile o t₁).prodMul (s.restProfile o t₂))) :
    (s.listener α μ o).real {t₁} < (s.listener α μ o).real {t₂} :=
  (s.listener_real_lt_iff_invPowSum hα hμeq hμ0
      (s.exists_of_fiberProfile_ne_zero fun h =>
        hcert.ne_zero (Multiset.prodMul_eq_zero_iff.mpr (Or.inl h)))).mpr
    (s.invPowSum_odds_lt_of_prodMul_strictDominates hα hcert)

/-- The evaluation register at a natural rationality: with all profile entries
dividing `D`, listener preference at equal priors is the ℕ-valued
common-denominator comparison — a kernel `decide`. The strict inequality
carries its own truth witness. -/
theorem listener_real_lt_of_divPowSum [s.Expressible] {k D : ℕ} (hk : k ≠ 0) (hD : D ≠ 0)
    {o : O} {t₁ t₂ : T} (hμeq : μ {t₁} = μ {t₂}) (hμ0 : μ {t₂} ≠ 0)
    (hdvd₁ : ∀ n ∈ s.profile t₁, n ∣ D) (hdvd₂ : ∀ n ∈ s.profile t₂, n ∣ D)
    (hlt : (s.fiberProfile o t₁).divPowSum D k * (s.profile t₂).divPowSum D k
      < (s.fiberProfile o t₂).divPowSum D k * (s.profile t₁).divPowSum D k) :
    (s.listener k μ o).real {t₁} < (s.listener k μ o).real {t₂} := by
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hfsub : ∀ t, ∀ n ∈ s.fiberProfile o t, n ∈ s.profile t := fun t n hn =>
    s.profile_eq_fiberProfile_add_restProfile o t ▸ Multiset.mem_add.mpr (Or.inl hn)
  have h₂ : s.fiberProfile o t₂ ≠ 0 :=
    Multiset.ne_zero_of_divPowSum_ne_zero
      (Nat.mul_ne_zero_iff.mp (Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) hlt))).1
  rw [s.listener_real_lt_iff_invPowSum hα hμeq hμ0 (s.exists_of_fiberProfile_ne_zero h₂)]
  have key : ∀ (m₁ m₂ : Multiset ℕ), (∀ n ∈ m₁, n ∣ D) → (∀ n ∈ m₂, n ∣ D) →
      (m₁.invPowSum k).toReal * (m₂.invPowSum k).toReal
        = (m₁.divPowSum D k * m₂.divPowSum D k : ℕ) / ((D : ℝ) ^ k) ^ 2 := by
    intro m₁ m₂ h₁ h₂
    rw [Multiset.invPowSum_toReal_eq hD k h₁, Multiset.invPowSum_toReal_eq hD k h₂]
    push_cast
    ring
  rw [key _ _ (fun n hn => hdvd₁ n (hfsub t₁ n hn)) hdvd₂,
    key _ _ (fun n hn => hdvd₂ n (hfsub t₂ n hn)) hdvd₁,
    div_lt_div_iff_of_pos_right (by positivity)]
  exact_mod_cast hlt

end Listener

end

/-! #### State-side latent families

[franke-bergen-2020] eqs. 11–13 (lexical uncertainty): each speaker carries a
fixed latent index and best-responds within it — normalization is per-index,
in contrast to the choice-side latents of `jointListener`, whose speaker
normalizes across the pooled pairs. The weight functions coincide; only the
normalization differs. -/

section Family

variable {T C O L : Type*} [MeasurableSpace T] [Fintype T] [DecidableEq T]
  [MeasurableSingletonClass T] [MeasurableSpace C] [Fintype C] [DiscreteMeasurableSpace C]
  [MeasurableSpace L] [Countable L] [MeasurableSingletonClass L]

/-- The family speaker: the latent index rides in the state. -/
noncomputable def familySpeaker (f : L → Scenario T C O) (α : ℝ) : Kernel (T × L) C :=
  Kernel.ofFunOfCountable fun tl => (f tl.2).speaker α tl.1

omit [DecidableEq T] in
@[simp] theorem familySpeaker_apply (f : L → Scenario T C O) (α : ℝ) (tl : T × L) :
    familySpeaker f α tl = (f tl.2).speaker α tl.1 := rfl

instance (f : L → Scenario T C O) (α : ℝ) : IsFiniteKernel (familySpeaker f α) :=
  ⟨⟨1, ENNReal.one_lt_top, fun tl => by
    rw [familySpeaker_apply]
    exact (f tl.2).speaker_apply_univ_le_one α tl.1⟩⟩

section

variable [StandardBorelSpace T] [Nonempty T] [StandardBorelSpace L] [Nonempty L]
  {μ : Measure (T × L)} [IsFiniteMeasure μ]

/-- The family listener: the Bayesian inverse of the family speaker over the
joint (state, index) space — [franke-bergen-2020] eqs. 12–13. Bundling the
posterior keeps consumers' goals first-order in `familyListener`. -/
noncomputable def familyListener (f : L → Scenario T C O) (α : ℝ)
    (μ : Measure (T × L)) [IsFiniteMeasure μ] : Kernel C (T × L) :=
  (familySpeaker f α)†μ

omit [StandardBorelSpace T] [Nonempty T] [StandardBorelSpace L] [Nonempty L] in
/-- A member's true choice at a positive-prior state witnesses a positive
observation marginal for the family speaker. -/
theorem comp_familySpeaker_ne_zero {f : L → Scenario T C O} {α : ℝ} (hα : 0 ≤ α)
    {μ : Measure (T × L)} (hμ0 : ∀ p : T × L, μ {p} ≠ 0) {t : T} {l : L} {c : C}
    (hmem : t ∈ (f l).sem c) : ((familySpeaker f α) ∘ₘ μ) {c} ≠ 0 :=
  comp_apply_singleton_ne_zero _ _ (hμ0 (t, l)) (by
    rw [familySpeaker_apply]
    exact (f l).speaker_apply_singleton_ne_zero hα hmem)

/-- State-marginal preference for a latent family at equal priors: the latent
pools, leaving summed member speaker shares. Any member's true choice at
either state supplies the positivity side condition. -/
theorem familyListener_fst_real_lt_iff [Fintype L] (f : L → Scenario T C O) {α : ℝ}
    (hα : 0 ≤ α) (hμeq : ∀ p q : T × L, μ {p} = μ {q}) (hμ0 : ∀ p : T × L, μ {p} ≠ 0)
    {c : C} {t₀ : T} {l₀ : L} (hmem : t₀ ∈ (f l₀).sem c) {t₁ t₂ : T} :
    ((familyListener f α μ) c).fst.real {t₁} < ((familyListener f α μ) c).fst.real {t₂}
      ↔ (∑ l, ((f l).speaker α t₁).real {c}) < ∑ l, ((f l).speaker α t₂).real {c} := by
  set p₀ : T × L := Classical.arbitrary _
  have key : ∀ t : T, (∑ l, μ.real {(t, l)} * ((familySpeaker f α) (t, l)).real {c})
      = μ.real {p₀} * ∑ l, ((f l).speaker α t).real {c} := fun t => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by
      rw [familySpeaker_apply, show μ.real {(t, l)} = μ.real {p₀} from by
        rw [measureReal_def, measureReal_def, hμeq (t, l) p₀]]
  rw [familyListener,
    posterior_fst_real_lt_iff _ _ (comp_familySpeaker_ne_zero hα hμ0 hmem), key, key,
    mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real {p₀} from ENNReal.toReal_pos (hμ0 p₀) (measure_ne_top _ _))]

/-- Latent-marginal preference for a latent family at equal priors: the
states pool, leaving summed member speaker shares. -/
theorem familyListener_snd_real_lt_iff (f : L → Scenario T C O) {α : ℝ}
    (hα : 0 ≤ α) (hμeq : ∀ p q : T × L, μ {p} = μ {q}) (hμ0 : ∀ p : T × L, μ {p} ≠ 0)
    {c : C} {t₀ : T} {l₀ : L} (hmem : t₀ ∈ (f l₀).sem c) {l₁ l₂ : L} :
    ((familyListener f α μ) c).snd.real {l₁} < ((familyListener f α μ) c).snd.real {l₂}
      ↔ (∑ t, ((f l₁).speaker α t).real {c}) < ∑ t, ((f l₂).speaker α t).real {c} := by
  set p₀ : T × L := Classical.arbitrary _
  have key : ∀ l : L, (∑ t, μ.real {(t, l)} * ((familySpeaker f α) (t, l)).real {c})
      = μ.real {p₀} * ∑ t, ((f l).speaker α t).real {c} := fun l => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by
      rw [familySpeaker_apply, show μ.real {(t, l)} = μ.real {p₀} from by
        rw [measureReal_def, measureReal_def, hμeq (t, l) p₀]]
  rw [familyListener,
    posterior_snd_real_lt_iff _ _ (comp_familySpeaker_ne_zero hα hμ0 hmem), key, key,
    mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real {p₀} from ENNReal.toReal_pos (hμ0 p₀) (measure_ne_top _ _))]

end

end Family

end Scenario

end RSA

