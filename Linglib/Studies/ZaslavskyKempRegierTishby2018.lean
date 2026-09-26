module

public import Linglib.Core.InformationTheory.ChannelCapacity
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Pragmatics.Efficiency

/-!
# Zaslavsky, Kemp, Regier and Tishby (2018): Efficient Compression in Color Naming

This file formalizes the communication model of [zaslavsky-kemp-regier-tishby-2018], in which
a color naming system is an encoder that compresses meanings, distributions over the colors of
the environment, into words, and languages are hypothesized to trade off the complexity of the
lexicon against the accuracy of communication as the Information Bottleneck principle of
[tishby-pereira-bialek-1999] prescribes. The meanings are a Markov kernel from `M` to the
environment `U`, the cognitive source a probability measure on `M`, and the encoder a Markov
kernel from `M` to the words `W`. The listener is the Bayesian decoder, interpreting a word as
the posterior mixture of meanings (`decoder`), and no other decoder has lower expected
distortion (`distortion_le`). Complexity is the information the words carry about the meanings
(`complexity`), accuracy the information they carry about the environment (`accuracy`), and the
expected Kullback–Leibler distortion between the speaker's meaning and the listener's
interpretation is the information about the environment that the lexicon loses
(`distortion_eq`), so that minimizing distortion is maximizing accuracy. Accuracy is bounded by
complexity and by the information the meanings carry (`accuracy_le_complexity`,
`accuracy_le_sourceInfo`), and a lexicon that ignores the meaning has complexity `0`
(`complexity_const`).

The Information Bottleneck objective `F_β = I(M;W) − β I(W;U)` (`objective`) is, up to a
constant, the β-scalarized cost of `Pragmatics.Efficiency` on the pair of distortion and
complexity (`objective_eq_weightedCost`), and a language's deviation from optimality at `β` is
the substrate's `efficiencyLossAt` (`deviation_eq_efficiencyLossAt`). Below `β = 1` the
meaning-blind lexicon is optimal (`objective_const_le`). Every minimizer of `F_β` has the
self-consistent Boltzmann form in which a word's probability decays exponentially in its
divergence from the meaning (`IsIBOptimum`, `isIBOptimum_of_forall_objective_le`), so that at
finite `β` the optimal categories are soft (`IsIBOptimum.real_pos`).

## Implementation notes

* The information quantities are the mutual informations `Im[·]` of `InformationTheory`, and
  the distortion the divergences `klDiv` of mathlib; the paper's forms with the word marginal in
  the denominator are the averaged divergences of `InformationTheory.measureMutualInfo_compProd`
  (`complexity_eq`). On finite alphabets no positivity assumption is needed: a meaning and a word
  that co-occur make the meaning absolutely continuous with respect to the word's
  interpretation.
* `distortion_eq` and `distortion_le` are the compensation identity
  `InformationTheory.sum_mul_toReal_klDiv` for the meanings channel, applied at each word's
  posterior over meanings.
* `isIBOptimum_of_forall_objective_le` is proved variationally: `F_β + β I(M;U)` is bounded
  above by the encoder's average divergence from a reference word marginal plus `β` times its
  expected distortion under a reference decoder, with equality at its own marginal and Bayesian
  decoder, and for fixed references the bound is least at the Boltzmann encoder. It assumes a
  source and meanings of full support, as the paper's Gaussian meanings are.
* The efficiency loss `ε_l` divides the minimal deviation by the fitted `β_l`; the fit itself is
  a numerical optimization outside the formalization. The empirical encoders of the World Color
  Survey are not in the library.

## References

* [N. Zaslavsky, C. Kemp, T. Regier and N. Tishby, *Efficient compression in color naming and
  its evolution* (2018)][zaslavsky-kemp-regier-tishby-2018]
* [N. Tishby, F. C. Pereira and W. Bialek, *The information bottleneck method*
  (1999)][tishby-pereira-bialek-1999]
* [C. E. Shannon, *A Mathematical Theory of Communication* (1948)][shannon-1948]
-/

@[expose] public section

namespace ZaslavskyKempRegierTishby2018

open MeasureTheory ProbabilityTheory InformationTheory Pragmatics.Efficiency Finset Real
open scoped ENNReal

variable {U M W : Type*} [MeasurableSpace U] [MeasurableSpace M] [MeasurableSpace W]
  [Fintype M] [MeasurableSingletonClass M] [Nonempty M]
  (meanings : Kernel M U) [IsMarkovKernel meanings] (source : Measure M)
  [IsProbabilityMeasure source] (encoder : Kernel M W) [IsMarkovKernel encoder]

/-! ### The Bayesian listener -/

/-- The listener's interpretation of a word (eq. 1), the posterior mixture of meanings
`m̂_w(u) = ∑ m, q(m | w) m(u)`. -/
noncomputable def decoder : Kernel W U := meanings ∘ₖ (encoder†source)

instance : IsMarkovKernel (decoder meanings source encoder) := by
  unfold decoder; infer_instance

omit [IsMarkovKernel meanings] in
/-- The interpretations, weighted by the word marginal, recover the environment marginal. -/
theorem decoder_comp :
    decoder meanings source encoder ∘ₘ (encoder ∘ₘ source) = meanings ∘ₘ source := by
  rw [decoder, ← Measure.comp_assoc, posterior_comp_self]

/-! ### Complexity, accuracy and distortion -/

variable [Fintype U] [Fintype W] [MeasurableSingletonClass U] [MeasurableSingletonClass W]

/-- The complexity of the lexicon, `I_q(M;W)`. -/
noncomputable def complexity : ℝ := Im[source ⊗ₘ encoder]

/-- The accuracy of the lexicon, `I_q(W;U)`, between a word and the listener's interpretation. -/
noncomputable def accuracy : ℝ := Im[(encoder ∘ₘ source) ⊗ₘ decoder meanings source encoder]

/-- The information the meanings carry about the environment, `I(M;U)`, independent of the
encoder. -/
noncomputable def sourceInfo : ℝ := Im[source ⊗ₘ meanings]

/-- The expected distortion `E_q[D[m ‖ m̂_w]]` between the speaker's meaning and the listener's
interpretation (eq. 4). -/
noncomputable def distortion : ℝ :=
  ∫ p, (klDiv (meanings p.1) (decoder meanings source encoder p.2)).toReal ∂(source ⊗ₘ encoder)

omit [Nonempty M] in
/-- Complexity in the paper's form (eq. 2): the source average of the divergence of each
meaning's naming distribution from the word marginal. -/
theorem complexity_eq :
    complexity source encoder
      = ∑ m, source.real {m} * (klDiv (encoder m) (encoder ∘ₘ source)).toReal :=
  measureMutualInfo_compProd encoder source

omit [Nonempty M] in
/-- A lexicon that ignores the meaning, such as a single word for every meaning, has the minimal
complexity `0`. -/
theorem complexity_const (ν : Measure W) [IsProbabilityMeasure ν] :
    complexity source (Kernel.const M ν) = 0 := by
  rw [complexity, Measure.compProd_const, measureMutualInfo_prod]

omit [Nonempty M] in
private theorem integral_compProd (f : M × W → ℝ) :
    ∫ p, f p ∂(source ⊗ₘ encoder)
      = ∑ m, source.real {m} * ∑ w, (encoder m).real {w} * f (m, w) := by
  rw [integral_fintype .of_finite, Fintype.sum_prod_type]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun w _ => ?_
  rw [Measure.compProd_real_singleton, smul_eq_mul, mul_assoc]

omit [Fintype W] in
private theorem comp_real_mul_posterior_real (m : M) (w : W) :
    (encoder ∘ₘ source).real {w} * ((encoder†source) w).real {m}
      = source.real {m} * (encoder m).real {w} := by
  obtain hw | hw := eq_or_ne ((encoder ∘ₘ source) {w}) 0
  · have h0 : source {m} * encoder m {w} = 0 := by
      rw [Measure.comp_apply_singleton, sum_eq_zero_iff] at hw
      exact hw m (mem_univ m)
    rw [measureReal_def, hw, ENNReal.toReal_zero, zero_mul, measureReal_def, measureReal_def,
      ← ENNReal.toReal_mul, h0, ENNReal.toReal_zero]
  · rw [posterior_real_singleton encoder source hw, mul_div_cancel₀]
    rwa [Ne, measureReal_eq_zero_iff (measure_ne_top _ _)]

/-- Reweighting each word's posterior over meanings by the word marginal recovers the joint
distribution of meanings and words. -/
private theorem integral_compProd_eq_sum_posterior (f : M × W → ℝ) :
    ∫ p, f p ∂(source ⊗ₘ encoder)
      = ∑ w, (encoder ∘ₘ source).real {w} * ∑ m, ((encoder†source) w).real {m} * f (m, w) := by
  rw [integral_compProd]
  simp_rw [mul_sum, ← mul_assoc, comp_real_mul_posterior_real]
  exact sum_comm

omit [Fintype W] [MeasurableSingletonClass W] in
/-- At each word, the posterior average of the divergences of the meanings from a reference
measure exceeds the average from the word's interpretation by the divergence of the
interpretation from the reference. -/
private theorem sum_posterior_toReal_klDiv (w : W) (ν : Measure U) [IsProbabilityMeasure ν]
    (hν : ∀ m, (encoder†source) w {m} ≠ 0 → meanings m ≪ ν) :
    ∑ m, ((encoder†source) w).real {m} * (klDiv (meanings m) ν).toReal
      = ∑ m, ((encoder†source) w).real {m}
          * (klDiv (meanings m) (decoder meanings source encoder w)).toReal
        + (klDiv (decoder meanings source encoder w) ν).toReal := by
  have hd : decoder meanings source encoder w = meanings ∘ₘ (encoder†source) w := rfl
  rw [hd, sum_mul_toReal_klDiv meanings _ ν hν, ← measureMutualInfo_compProd]

/-- Eq. 5: the expected distortion is the information about the environment that the lexicon
loses, `E_q[D[M ‖ M̂]] = I(M;U) − I_q(W;U)`. -/
theorem distortion_eq :
    distortion meanings source encoder
      = sourceInfo meanings source - accuracy meanings source encoder := by
  have hsrc : sourceInfo meanings source
      = ∫ p, (klDiv (meanings p.1) (meanings ∘ₘ source)).toReal ∂(source ⊗ₘ encoder) := by
    rw [sourceInfo, measureMutualInfo_compProd, integral_compProd]
    refine sum_congr rfl fun m _ => ?_
    dsimp only
    rw [← sum_mul, sum_measureReal_singleton, coe_univ, probReal_univ, one_mul]
  rw [eq_sub_iff_add_eq, distortion, hsrc, accuracy, measureMutualInfo_compProd, decoder_comp,
    integral_compProd_eq_sum_posterior, integral_compProd_eq_sum_posterior, ← sum_add_distrib]
  refine sum_congr rfl fun w _ => ?_
  dsimp only
  obtain hw | hw := eq_or_ne ((encoder ∘ₘ source) {w}) 0
  · simp [measureReal_def, hw]
  rw [← mul_add, sum_posterior_toReal_klDiv meanings source encoder w (meanings ∘ₘ source)
    fun m hm => meanings.absolutelyContinuous_comp source fun h => hm ?_]
  rw [posterior_apply_singleton encoder source hw, h, zero_mul, ENNReal.zero_div]

/-- The Bayesian listener of eq. 1 is optimal: no decoder whose interpretations allow every
state that a meaning allows has lower expected distortion. -/
theorem distortion_le (d : Kernel W U) [IsMarkovKernel d] (hd : ∀ m w, meanings m ≪ d w) :
    distortion meanings source encoder
      ≤ ∫ p, (klDiv (meanings p.1) (d p.2)).toReal ∂(source ⊗ₘ encoder) := by
  rw [distortion, integral_compProd_eq_sum_posterior, integral_compProd_eq_sum_posterior]
  refine sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
  dsimp only
  rw [sum_posterior_toReal_klDiv meanings source encoder w (d w) fun m _ => hd m w]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

/-! ### The information plane -/

/-- Accuracy is bounded by the information the meanings carry about the environment. -/
theorem accuracy_le_sourceInfo : accuracy meanings source encoder ≤ sourceInfo meanings source := by
  have : 0 ≤ distortion meanings source encoder := integral_nonneg fun _ => ENNReal.toReal_nonneg
  linarith [distortion_eq meanings source encoder]

/-- Accuracy is bounded by complexity: the words carry no more information about the environment
than about the meanings they compress. -/
theorem accuracy_le_complexity : accuracy meanings source encoder ≤ complexity source encoder := by
  rw [accuracy, complexity, decoder, ← Measure.parallelComp_comp_compProd,
    ← measureMutualInfo_map_swap (source ⊗ₘ encoder), ← compProd_posterior_eq_map_swap]
  exact measureMutualInfo_parallelComp_id_comp_le _ meanings

/-! ### The Information Bottleneck objective -/

/-- The Information Bottleneck objective (eq. 6), `F_β = I_q(M;W) − β I_q(W;U)`. -/
noncomputable def objective (β : ℝ) : ℝ :=
  complexity source encoder - β * accuracy meanings source encoder

/-- The distortion–complexity cost pair of the lexicon. -/
noncomputable def costPair : CostPair :=
  ⟨distortion meanings source encoder, complexity source encoder⟩

/-- Up to the encoder-independent constant `β I(M;U)`, the objective is the β-scalarized cost
of distortion and complexity. -/
theorem objective_eq_weightedCost (β : ℝ) :
    objective meanings source encoder β
      = weightedCost (costPair meanings source encoder) β - β * sourceInfo meanings source := by
  rw [objective, weightedCost, costPair, distortion_eq]
  ring

/-- For `β ≤ 1` the objective is minimized by a lexicon that ignores the meaning, at `0`: the
IB optima are informative only above `β = 1`, and eq. 6 takes `β ≥ 1`. -/
theorem objective_const_le (ν : Measure W) [IsProbabilityMeasure ν] {β : ℝ} (hβ : β ≤ 1) :
    objective meanings source (Kernel.const M ν) β ≤ objective meanings source encoder β := by
  have h0 : accuracy meanings source (Kernel.const M ν) = 0 :=
    le_antisymm ((accuracy_le_complexity ..).trans (complexity_const source ν).le)
      (measureMutualInfo_nonneg _)
  have h1 := accuracy_le_complexity meanings source encoder
  have h2 : 0 ≤ accuracy meanings source encoder := measureMutualInfo_nonneg _
  rw [objective, objective, complexity_const, h0]
  nlinarith [mul_nonneg (sub_nonneg.2 hβ) h2]

/-- The self-consistent form of the Information Bottleneck optima (eq. 7): each word's
probability decays exponentially, at rate `β`, in the divergence between the meaning and the
word's interpretation. -/
def IsIBOptimum (β : ℝ) : Prop :=
  ∀ m w, (encoder m).real {w} =
    (encoder ∘ₘ source).real {w}
        * exp (-β * (klDiv (meanings m) (decoder meanings source encoder w)).toReal)
      / ∑ w', (encoder ∘ₘ source).real {w'}
        * exp (-β * (klDiv (meanings m) (decoder meanings source encoder w')).toReal)

omit [IsMarkovKernel meanings] [Fintype U] [MeasurableSingletonClass U]
  [MeasurableSingletonClass W] in
/-- At finite `β` the IB optima induce soft categories: a word in use has positive probability
under every meaning. -/
theorem IsIBOptimum.real_pos {β : ℝ} (h : IsIBOptimum meanings source encoder β) {w : W}
    (hw : (encoder ∘ₘ source) {w} ≠ 0) (m : M) : 0 < (encoder m).real {w} := by
  set g := fun w' => (encoder ∘ₘ source).real {w'}
    * exp (-β * (klDiv (meanings m) (decoder meanings source encoder w')).toReal)
  have hg : 0 < g w := mul_pos (ENNReal.toReal_pos hw (measure_ne_top _ _)) (exp_pos _)
  rw [h m w]
  exact div_pos hg (hg.trans_le (single_le_sum (fun _ _ => by positivity) (mem_univ w)))

/-- Eq. 7: for a source and meanings of full support, every minimizer of the objective at
`β ≥ 0` has the self-consistent Boltzmann form. -/
theorem isIBOptimum_of_forall_objective_le {β : ℝ} (hβ : 0 ≤ β)
    (hsource : ∀ m, source {m} ≠ 0) (hmeanings : ∀ m u, meanings m {u} ≠ 0)
    (hmin : ∀ (q : Kernel M W) [IsMarkovKernel q],
      objective meanings source encoder β ≤ objective meanings source q β) :
    IsIBOptimum meanings source encoder β := by
  classical
  have hreal {ν : Measure W} [IsFiniteMeasure ν] {w : W} : ν.real {w} = 0 ↔ ν {w} = 0 :=
    measureReal_eq_zero_iff (measure_ne_top _ _)
  have hone (ν : Measure W) [IsProbabilityMeasure ν] : ∑ w, ν.real {w} = 1 := by
    rw [sum_measureReal_singleton, coe_univ, probReal_univ]
  -- the interpretations have full support, so every meaning is absolutely continuous to each
  have hdac (m : M) (w : W) : meanings m ≪ decoder meanings source encoder w := by
    refine Measure.absolutelyContinuous_of_forall_singleton fun u hu => absurd hu ?_
    obtain ⟨m', hm'⟩ : ∃ m', (encoder†source) w {m'} ≠ 0 := by
      by_contra! h
      have := measure_univ (μ := (encoder†source) w)
      rw [← coe_univ, ← sum_measure_singleton, sum_eq_zero fun m' _ => h m'] at this
      exact zero_ne_one this
    rw [show decoder meanings source encoder w {u} = _ from
      Kernel.comp_apply_singleton meanings (encoder†source) w u]
    exact fun h => mul_ne_zero hm' (hmeanings m' u) (sum_eq_zero_iff.1 h m' (mem_univ m'))
  obtain ⟨D, hD⟩ : ∃ D : M → W → ℝ,
      D = fun m w => (klDiv (meanings m) (decoder meanings source encoder w)).toReal := ⟨_, rfl⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w, 0 < (encoder ∘ₘ source).real {w} := by
    by_contra! h
    linarith [sum_nonpos fun w (_ : w ∈ univ) => h w, hone (encoder ∘ₘ source)]
  have hnn (m : M) (w : W) : 0 ≤ (encoder ∘ₘ source).real {w} * exp (-β * D m w) :=
    mul_nonneg measureReal_nonneg (exp_pos _).le
  obtain ⟨Z, hZ⟩ : ∃ Z : M → ℝ,
      Z = fun m => ∑ w, (encoder ∘ₘ source).real {w} * exp (-β * D m w) := ⟨_, rfl⟩
  have hZpos (m : M) : 0 < Z m := by
    rw [hZ]
    exact (mul_pos hw₀ (exp_pos _)).trans_le (single_le_sum (fun w _ => hnn m w) (mem_univ w₀))
  -- the Boltzmann encoder of eq. 7 built from the minimizer's word marginal and interpretations
  obtain ⟨g, hgdef⟩ : ∃ g : Kernel M W, g = Kernel.ofWeights fun m w =>
      ENNReal.ofReal ((encoder ∘ₘ source).real {w} * exp (-β * D m w)) := ⟨_, rfl⟩
  have : IsMarkovKernel g := hgdef ▸ Kernel.isMarkovKernel_ofWeights
    (fun _ => ⟨w₀, fun h => (mul_pos hw₀ (exp_pos _)).not_ge (ENNReal.ofReal_eq_zero.1 h)⟩)
    fun _ _ => ENNReal.ofReal_ne_top
  have hg (m : M) (w : W) :
      (g m).real {w} = (encoder ∘ₘ source).real {w} * exp (-β * D m w) / Z m := by
    rw [hgdef, Kernel.ofWeights_real_singleton _ m fun _ => ENNReal.ofReal_ne_top, hZ]
    simp only [ENNReal.toReal_ofReal (hnn _ _)]
  have hq_r (m : M) : encoder m ≪ encoder ∘ₘ source :=
    encoder.absolutelyContinuous_comp source (hsource m)
  have hr_g (m : M) : encoder ∘ₘ source ≪ g m :=
    Measure.absolutelyContinuous_of_forall_singleton fun w hw => by
      have h1 := (hreal (ν := g m)).2 hw
      rw [hg, div_eq_zero_iff, mul_eq_zero] at h1
      exact hreal.1 ((h1.resolve_right (hZpos m).ne').resolve_right (exp_pos _).ne')
  have hg_r (m : M) : g m ≪ encoder ∘ₘ source :=
    Measure.absolutelyContinuous_of_forall_singleton fun w hw => by
      rw [← hreal, hg, hreal.2 hw, zero_mul, zero_div]
  -- Gibbs: the divergence from the marginal plus the expected distortion is the divergence from
  -- the Boltzmann row, less its log normalizer
  have hgibbs (ν : Measure W) [IsProbabilityMeasure ν] (hν : ν ≪ encoder ∘ₘ source) (m : M) :
      (klDiv ν (encoder ∘ₘ source)).toReal + β * ∑ w, ν.real {w} * D m w
        = (klDiv ν (g m)).toReal - log (Z m) := by
    rw [toReal_klDiv_eq_sum_log_div hν, toReal_klDiv_eq_sum_log_div (hν.trans (hr_g m)),
      show log (Z m) = ∑ w, ν.real {w} * log (Z m) by rw [← sum_mul, hone, one_mul],
      mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun w _ => ?_
    obtain hx | hx := eq_or_ne (ν.real {w}) 0
    · simp [hx]
    have hr : (encoder ∘ₘ source).real {w} ≠ 0 := fun h => hx (hreal.2 (hν (hreal.1 h)))
    rw [hg, log_div hx (div_ne_zero (mul_ne_zero hr (exp_pos _).ne') (hZpos m).ne'),
      log_div (mul_ne_zero hr (exp_pos _).ne') (hZpos m).ne', log_mul hr (exp_pos _).ne', log_exp,
      log_div hx hr]
    ring
  -- the variational functional at the minimizer is its objective, and at the Boltzmann
  -- encoder it bounds the Boltzmann encoder's objective
  have hsplit (q : Kernel M W) : ∑ m, source.real {m}
        * ((klDiv (q m) (encoder ∘ₘ source)).toReal + β * ∑ w, (q m).real {w} * D m w)
      = ∑ m, source.real {m} * (klDiv (q m) (encoder ∘ₘ source)).toReal
        + β * ∑ m, source.real {m} * ∑ w, (q m).real {w} * D m w := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  have hLq : objective meanings source encoder β + β * sourceInfo meanings source
      = ∑ m, source.real {m}
        * ((klDiv (encoder m) (encoder ∘ₘ source)).toReal + β * ∑ w, (encoder m).real {w} * D m w)
      := by
    have h2 : distortion meanings source encoder
        = ∑ m, source.real {m} * ∑ w, (encoder m).real {w} * D m w := by
      rw [distortion, integral_compProd, hD]
    rw [hsplit, ← complexity_eq, ← h2, objective, distortion_eq]
    ring
  have hLg : objective meanings source g β + β * sourceInfo meanings source
      ≤ ∑ m, source.real {m}
        * ((klDiv (g m) (encoder ∘ₘ source)).toReal + β * ∑ w, (g m).real {w} * D m w) := by
    have h1 := sum_mul_toReal_klDiv g source (encoder ∘ₘ source) fun m _ => hg_r m
    have h2 : distortion meanings source g
        ≤ ∑ m, source.real {m} * ∑ w, (g m).real {w} * D m w := by
      have := distortion_le meanings source g (decoder meanings source encoder) hdac
      rw [integral_compProd] at this
      rw [hD]
      exact this
    have h3 := distortion_eq meanings source g
    have h4 : 0 ≤ (klDiv (g ∘ₘ source) (encoder ∘ₘ source)).toReal := ENNReal.toReal_nonneg
    rw [hsplit, h1, objective, complexity]
    nlinarith [mul_le_mul_of_nonneg_left h2 hβ]
  have hq := sum_congr rfl fun m (_ : m ∈ univ) =>
    congrArg (source.real {m} * ·) (hgibbs (encoder m) (hq_r m) m)
  have hgg := sum_congr rfl fun m (_ : m ∈ univ) =>
    congrArg (source.real {m} * ·) (hgibbs (g m) (hg_r m) m)
  simp only [klDiv_self, ENNReal.toReal_zero, zero_sub, mul_sub, sum_sub_distrib] at hq hgg
  have hsum : ∑ m, source.real {m} * (klDiv (encoder m) (g m)).toReal ≤ 0 := by
    have := hmin g
    simp only [mul_neg, sum_neg_distrib] at hgg
    linarith
  have hnn' (m : M) : 0 ≤ source.real {m} * (klDiv (encoder m) (g m)).toReal :=
    mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg
  intro m w
  have hterm := (sum_eq_zero_iff_of_nonneg fun m _ => hnn' m).1
    (le_antisymm hsum (sum_nonneg fun m _ => hnn' m)) m (mem_univ m)
  have hkl : klDiv (encoder m) (g m) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1
      ((mul_eq_zero.1 hterm).resolve_left
        (mt (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (hsource m))) with h | h
    · exact h
    · exact absurd h (klDiv_eq_top_iff_not_ac.not.2 (not_not.2 ((hq_r m).trans (hr_g m))))
  rw [klDiv_eq_zero_iff.1 hkl, hg, hZ, hD]

variable (encoder' : Kernel M W) [IsMarkovKernel encoder']

/-- The deviation `ΔF_β` of the lexicon from a reference encoder at `β`. -/
noncomputable def deviation (β : ℝ) : ℝ :=
  objective meanings source encoder β - objective meanings source encoder' β

/-- The deviation of the lexicon from a reference encoder over the same meanings and source is
the substrate's efficiency loss at `β`. -/
theorem deviation_eq_efficiencyLossAt (β : ℝ) :
    deviation meanings source encoder encoder' β = efficiencyLossAt
      (costPair meanings source encoder) (costPair meanings source encoder') β := by
  rw [deviation, efficiencyLossAt, objective_eq_weightedCost, objective_eq_weightedCost]
  ring

/-- The efficiency loss `ε_l = ΔF_{β_l} / β_l` at the fitted trade-off. -/
noncomputable def efficiencyLoss (β : ℝ) : ℝ :=
  deviation meanings source encoder encoder' β / β

omit [IsMarkovKernel meanings] [Fintype U] [Fintype W] [MeasurableSingletonClass U]
  [MeasurableSingletonClass W] in
/-- Against an optimal encoder at a positive `β`, the efficiency loss is nonnegative. -/
theorem efficiencyLoss_nonneg {β : ℝ} (hβ : 0 < β)
    (hmin : ∀ (q : Kernel M W) [IsMarkovKernel q],
      objective meanings source encoder' β ≤ objective meanings source q β) :
    0 ≤ efficiencyLoss meanings source encoder encoder' β :=
  div_nonneg (sub_nonneg.2 (hmin encoder)) hβ.le

end ZaslavskyKempRegierTishby2018
