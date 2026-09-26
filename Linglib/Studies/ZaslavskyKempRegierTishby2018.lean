module

public import Linglib.Core.InformationTheory.ChannelCapacity
public import Linglib.Pragmatics.Efficiency

/-!
# Zaslavsky, Kemp, Regier and Tishby (2018): Efficient Compression in Color Naming

This file formalizes the communication model of [zaslavsky-kemp-regier-tishby-2018], in which
a color naming system is an encoder that compresses meanings, distributions over the colors of
the environment, into words, and languages are hypothesized to trade off the complexity of the
lexicon against the accuracy of communication as the Information Bottleneck principle of
[tishby-pereira-bialek-1999] prescribes. The meanings are a Markov kernel from `M` to the
environment `U`, the cognitive source a probability measure on `M`, and the encoder a Markov
kernel from `M` to the words `W`. The listener is an optimal Bayesian decoder, interpreting a
word as the posterior mixture of meanings (`decoder`). Complexity is the information the words
carry about the meanings (`complexity`), accuracy the information they carry about the
environment (`accuracy`), and the expected Kullback–Leibler distortion between the speaker's
meaning and the listener's interpretation is the information about the environment that the
lexicon loses (`distortion_eq`), so that minimizing distortion is maximizing accuracy. The
Information Bottleneck objective `F_β = I(M;W) − β I(W;U)` (`objective`) is, up to a constant,
the β-scalarized cost of `Pragmatics.Efficiency` on the pair of distortion and complexity
(`objective_eq_weightedCost`), and a language's deviation from optimality at `β` is the
substrate's `efficiencyLossAt` (`deviation_eq_efficiencyLossAt`). The optimal encoders satisfy
the self-consistent Boltzmann form in which a word's probability decays exponentially in its
divergence from the meaning (`IsIBOptimum`).

## Implementation notes

* The information quantities are the mutual informations `Im[·]` of `InformationTheory`, and
  the distortion the divergences `klDiv` of mathlib; the paper's forms with the word marginal in
  the denominator are the averaged divergences of `InformationTheory.measureMutualInfo_compProd`
  (`complexity_eq`). On finite alphabets no positivity assumption is needed: a meaning and a word
  that co-occur make the meaning absolutely continuous with respect to the word's
  interpretation.
* `distortion_eq` is the compensation identity `InformationTheory.sum_mul_toReal_klDiv` for the
  meanings channel, applied at each word's posterior over meanings.
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

/-- The listener's interpretation of a word, the posterior mixture of meanings
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
interpretation. -/
noncomputable def distortion : ℝ :=
  ∫ p, (klDiv (meanings p.1) (decoder meanings source encoder p.2)).toReal ∂(source ⊗ₘ encoder)

omit [Nonempty M] in
/-- Complexity in the paper's form: the source average of the divergence of each meaning's
naming distribution from the word marginal. -/
theorem complexity_eq :
    complexity source encoder
      = ∑ m, source.real {m} * (klDiv (encoder m) (encoder ∘ₘ source)).toReal :=
  measureMutualInfo_compProd encoder source

/-- The expected distortion is the information about the environment that the lexicon loses:
`E_q[D[M ‖ M̂]] = I(M;U) − I_q(W;U)`. -/
theorem distortion_eq :
    distortion meanings source encoder
      = sourceInfo meanings source - accuracy meanings source encoder := by
  -- at each word, the posterior average of the divergences of the meanings from the environment
  -- marginal exceeds that from the interpretation by the divergence between the two
  have hword (w : W) (hw : (encoder ∘ₘ source) {w} ≠ 0) :
      ∑ m, ((encoder†source) w).real {m}
          * ((klDiv (meanings m) (meanings ∘ₘ source)).toReal
            - (klDiv (meanings m) (decoder meanings source encoder w)).toReal)
        = (klDiv (decoder meanings source encoder w) (meanings ∘ₘ source)).toReal := by
    have hac (m : M) (hm : (encoder†source) w {m} ≠ 0) : meanings m ≪ meanings ∘ₘ source := by
      refine meanings.absolutelyContinuous_comp source fun h => hm ?_
      rw [posterior_apply_singleton encoder source hw, h, zero_mul, ENNReal.zero_div]
    have hd : decoder meanings source encoder w = meanings ∘ₘ (encoder†source) w := rfl
    simp only [hd, mul_sub, sum_sub_distrib]
    rw [sum_mul_toReal_klDiv meanings ((encoder†source) w) _ hac,
      ← measureMutualInfo_compProd meanings ((encoder†source) w)]
    ring
  -- reweighting the posteriors by the word marginal recovers the joint of meanings and words
  have hbayes (m : M) (w : W) :
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
  have hsrc : sourceInfo meanings source = ∑ m, ∑ w, source.real {m} * (encoder m).real {w}
      * (klDiv (meanings m) (meanings ∘ₘ source)).toReal := by
    rw [sourceInfo, measureMutualInfo_compProd]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_mul, ← mul_sum, sum_measureReal_singleton, coe_univ, probReal_univ, mul_one]
  have hacc : accuracy meanings source encoder = ∑ w, (encoder ∘ₘ source).real {w}
      * ∑ m, ((encoder†source) w).real {m}
        * ((klDiv (meanings m) (meanings ∘ₘ source)).toReal
          - (klDiv (meanings m) (decoder meanings source encoder w)).toReal) := by
    rw [accuracy, measureMutualInfo_compProd, decoder_comp]
    refine sum_congr rfl fun w _ => ?_
    obtain hw | hw := eq_or_ne ((encoder ∘ₘ source) {w}) 0
    · rw [measureReal_def, hw, ENNReal.toReal_zero, zero_mul, zero_mul]
    · rw [hword w hw]
  simp_rw [mul_sum, ← mul_assoc, hbayes] at hacc
  rw [distortion, integral_fintype .of_finite, Fintype.sum_prod_type, hsrc, hacc, sum_comm
    (f := fun w m => source.real {m} * (encoder m).real {w} * _), ← sum_sub_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun w _ => ?_
  rw [Measure.compProd_real_singleton, smul_eq_mul]
  ring

/-! ### The Information Bottleneck objective -/

/-- The Information Bottleneck objective `F_β = I_q(M;W) − β I_q(W;U)`. -/
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

/-- The self-consistent form of the Information Bottleneck optima: each word's probability
decays exponentially, at rate `β`, in the divergence between the meaning and the word's
interpretation. -/
def IsIBOptimum (β : ℝ) : Prop :=
  ∀ m w, (encoder m).real {w} =
    (encoder ∘ₘ source).real {w}
        * exp (-β * (klDiv (meanings m) (decoder meanings source encoder w)).toReal)
      / ∑ w', (encoder ∘ₘ source).real {w'}
        * exp (-β * (klDiv (meanings m) (decoder meanings source encoder w')).toReal)

end ZaslavskyKempRegierTishby2018
