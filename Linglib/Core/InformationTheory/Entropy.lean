/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.InformationTheory.KullbackLeibler.Finite
import Linglib.Core.MeasureTheory.Measure.Prod
import Linglib.Core.Probability.Kernel.Composition.Lemmas
import Linglib.Core.Probability.UniformOn
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Entropy of a measure

The Shannon entropy of a measure on a measurable space, following the PFR project's
`ForMathlib` entropy: `Hm[μ] = ∑' s, negMulLog (((μ univ)⁻¹ • μ).real {s})`, normalized so
that a finite measure has the entropy of its probability normalization. Mutual information is
the entropy difference `Im[μ] = Hm[μ.fst] + Hm[μ.snd] - Hm[μ]`; on a finite type it is the
real part of the Kullback–Leibler divergence of the joint from the product of its marginals,
hence nonnegative.

Random variables carry the same quantities through their laws: `H[X ; μ] = Hm[μ.map X]`,
the conditional entropy `H[X | Y ; μ]` as the expected entropy of `X` under `Y = y`, and
`I[X : Y ; μ]`; on finite types the chain rule `H[X, Y] = H[Y] + H[X | Y]` holds and
conditioning reduces entropy.

## Main definitions

* `measureEntropy`, notation `Hm[μ]`; `measureMutualInfo`, notation `Im[μ]`
* `entropy`, notation `H[X ; μ]`; `condEntropy`, notation `H[X | Y ; μ]`;
  `mutualInfo`, notation `I[X : Y ; μ]`

## Main results

* `measureEntropy_le_log_card`: entropy is at most the log of the cardinality;
  `measureEntropy_uniformOn`: the uniform measure attains it.
* `measureMutualInfo_eq_toReal_klDiv`, `measureMutualInfo_nonneg`,
  `measureMutualInfo_parallelComp_id_comp_le` (data processing).
* `chain_rule`, `mutualInfo_eq_entropy_sub_condEntropy`, `condEntropy_le_entropy`.

## References

* [cover-thomas-2006], chapter 2.
* The PFR project, `PFR/ForMathlib/Entropy/Measure.lean`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal ProbabilityTheory

namespace InformationTheory

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

section measureEntropy

variable {μ : Measure S}

/-- Entropy of a measure. The measure is normalized by `(μ Set.univ)⁻¹`, so that a finite
measure has the entropy of its probability normalization and every other measure has entropy
`0`; on a probability measure `simp` removes the normalization. -/
noncomputable def measureEntropy (μ : Measure S) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})

@[inherit_doc measureEntropy] scoped notation:100 "Hm[" μ "]" => measureEntropy μ

@[simp] theorem measureEntropy_zero : Hm[(0 : Measure S)] = 0 := by simp [measureEntropy]

theorem measureEntropy_of_not_isFiniteMeasure (h : ¬ IsFiniteMeasure μ) : Hm[μ] = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]

theorem measureEntropy_of_isProbabilityMeasure (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, negMulLog (μ.real {s}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | _ <;> simp [measureEntropy]

theorem measureEntropy_eq_sum [Fintype S] (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑ s, negMulLog (μ.real {s}) := by
  rw [measureEntropy_of_isProbabilityMeasure, tsum_fintype]

theorem measureEntropy_univ_smul : Hm[(μ Set.univ)⁻¹ • μ] = Hm[μ] := by
  by_cases hμ : IsFiniteMeasure μ
  · rcases eq_zero_or_neZero μ with rfl | _
    · simp
    · simp [measureEntropy]
  · rw [measureEntropy_of_not_isFiniteMeasure hμ]
    rw [not_isFiniteMeasure_iff] at hμ
    simp [hμ]

theorem measureEntropy_nonneg (μ : Measure S) : 0 ≤ Hm[μ] := by
  by_cases hμ : IsFiniteMeasure μ
  · refine tsum_nonneg fun s => negMulLog_nonneg (by positivity) ?_
    rcases eq_zero_or_neZero μ with rfl | _
    · simp
    · exact measureReal_le_one
  · rw [measureEntropy_of_not_isFiniteMeasure hμ]

variable [MeasurableSingletonClass S]

@[simp] theorem measureEntropy_dirac (x : S) : Hm[Measure.dirac x] = 0 := by
  rw [measureEntropy_of_isProbabilityMeasure, tsum_eq_single x]
  · simp [measureReal_def]
  · intro y hy
    simp [measureReal_def, hy.symm]

private theorem measureEntropy_le_log_card_of_isProbabilityMeasure [Fintype S] (μ : Measure S)
    [IsProbabilityMeasure μ] : Hm[μ] ≤ log (Fintype.card S) := by
  have : Nonempty S := μ.nonempty_of_neZero
  set N := Fintype.card S
  have hN : (N : ℝ) ≠ 0 := by positivity
  rw [measureEntropy_eq_sum]
  calc ∑ s, negMulLog (μ.real {s}) = N * ∑ s, (N : ℝ)⁻¹ * negMulLog (μ.real {s}) := by
        rw [Finset.mul_sum]
        congr with s
        rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
    _ ≤ N * negMulLog (∑ s, (N : ℝ)⁻¹ * μ.real {s}) := by
        gcongr
        exact concaveOn_negMulLog.le_map_sum (by simp) (by simp [N]) (by simp)
    _ = N * negMulLog (N : ℝ)⁻¹ := by
        rw [← Finset.mul_sum, sum_measureReal_singleton, Finset.coe_univ, probReal_univ, mul_one]
    _ = log N := by simp [negMulLog, ← mul_assoc, mul_inv_cancel₀ hN]

/-- Entropy is at most the logarithm of the cardinality of the type. -/
theorem measureEntropy_le_log_card [Fintype S] (μ : Measure S) :
    Hm[μ] ≤ log (Fintype.card S) := by
  by_cases hμ : IsFiniteMeasure μ
  · rcases eq_zero_or_neZero μ with rfl | _
    · simpa using log_natCast_nonneg (Fintype.card S)
    · rw [← measureEntropy_univ_smul]
      exact measureEntropy_le_log_card_of_isProbabilityMeasure _
  · rw [measureEntropy_of_not_isFiniteMeasure hμ]
    exact log_natCast_nonneg _

/-- The entropy of the uniform measure on a finite set is the logarithm of its cardinality. -/
theorem measureEntropy_uniformOn [Fintype S] [DecidableEq S] {A : Finset S} (hA : A.Nonempty) :
    Hm[uniformOn (A : Set S)] = log A.card := by
  have := isProbabilityMeasure_uniformOn A.finite_toSet (by simpa using hA)
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  rw [measureEntropy_eq_sum]
  simp_rw [measureReal_def, uniformOn_finset_apply_singleton, apply_ite ENNReal.toReal,
    apply_ite negMulLog, ENNReal.toReal_zero, negMulLog_zero, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    negMulLog, log_inv]
  field_simp

end measureEntropy

section measureMutualInfo

/-- Mutual information of a measure on a product: the entropies of the marginals less the
entropy of the joint. -/
noncomputable def measureMutualInfo (μ : Measure (S × T)) : ℝ :=
  Hm[μ.fst] + Hm[μ.snd] - Hm[μ]

@[inherit_doc measureMutualInfo] scoped notation:100 "Im[" μ "]" => measureMutualInfo μ

variable [Fintype S] [Fintype T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  (μ : Measure (S × T)) [IsProbabilityMeasure μ]

/-- On a finite product, mutual information is the real part of the Kullback–Leibler
divergence of the joint from the product of its marginals. -/
theorem measureMutualInfo_eq_toReal_klDiv : Im[μ] = (klDiv μ (μ.fst.prod μ.snd)).toReal := by
  have h (a : S) (b : T) :
      μ.real {(a, b)} * log (μ.real {(a, b)} / (μ.fst.prod μ.snd).real {(a, b)})
        = -negMulLog (μ.real {(a, b)}) - μ.real {(a, b)} * log (μ.fst.real {a})
          - μ.real {(a, b)} * log (μ.snd.real {b}) := by
    rw [Measure.prod_real_singleton]
    obtain hp | hp := eq_or_ne (μ.real {(a, b)}) 0
    · simp [hp]
    · have hpos : 0 < μ.real {(a, b)} := lt_of_le_of_ne measureReal_nonneg hp.symm
      have ha : μ.real {(a, b)} ≤ μ.fst.real {a} := by
        rw [Measure.fst_real_singleton_eq_sum]
        exact Finset.single_le_sum (f := fun b => μ.real {(a, b)}) (fun _ _ => measureReal_nonneg)
          (Finset.mem_univ b)
      have hb : μ.real {(a, b)} ≤ μ.snd.real {b} := by
        rw [Measure.snd_real_singleton_eq_sum]
        exact Finset.single_le_sum (f := fun a => μ.real {(a, b)}) (fun _ _ => measureReal_nonneg)
          (Finset.mem_univ a)
      rw [log_div hp (mul_ne_zero (hpos.trans_le ha).ne' (hpos.trans_le hb).ne'),
        log_mul (hpos.trans_le ha).ne' (hpos.trans_le hb).ne', negMulLog]
      ring
  have h1 : ∑ a, ∑ b, μ.real {(a, b)} * log (μ.fst.real {a})
      = ∑ a, μ.fst.real {a} * log (μ.fst.real {a}) := by
    simp_rw [← Finset.sum_mul, ← Measure.fst_real_singleton_eq_sum]
  have h2 : ∑ a, ∑ b, μ.real {(a, b)} * log (μ.snd.real {b})
      = ∑ b, μ.snd.real {b} * log (μ.snd.real {b}) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Measure.snd_real_singleton_eq_sum]
  rw [toReal_klDiv_eq_sum_log_div μ.absolutelyContinuous_fst_prod_snd,
    measureMutualInfo, measureEntropy_eq_sum, measureEntropy_eq_sum, measureEntropy_eq_sum]
  simp_rw [Fintype.sum_prod_type, h, Finset.sum_sub_distrib, Finset.sum_neg_distrib, h1, h2,
    negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

theorem measureMutualInfo_nonneg : 0 ≤ Im[μ] := by
  rw [measureMutualInfo_eq_toReal_klDiv]
  exact ENNReal.toReal_nonneg

/-- **Data processing**: pushing the second coordinate through a Markov kernel cannot increase
mutual information. -/
theorem measureMutualInfo_parallelComp_id_comp_le {U : Type*} [MeasurableSpace U] [Fintype U]
    [MeasurableSingletonClass U] (η : Kernel T U) [IsMarkovKernel η] :
    Im[(Kernel.id ∥ₖ η) ∘ₘ μ] ≤ Im[μ] := by
  have : Nonempty T := μ.nonempty_of_neZero.map Prod.snd
  rw [measureMutualInfo_eq_toReal_klDiv, measureMutualInfo_eq_toReal_klDiv,
    Measure.fst_parallelComp_id_comp, Measure.snd_parallelComp_id_comp,
    ← Measure.parallelComp_id_comp_prod]
  exact ENNReal.toReal_mono
    (klDiv_ne_top_iff.mpr ⟨μ.absolutelyContinuous_fst_prod_snd, .of_finite⟩)
    (klDiv_comp_right_le _ _ _)

end measureMutualInfo

section entropy

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → S} {Y : Ω → T}

/-- Entropy of a random variable: the entropy of its law. -/
noncomputable def entropy (X : Ω → S) (μ : Measure Ω) : ℝ := Hm[μ.map X]

@[inherit_doc entropy] scoped notation3:max "H[" X " ; " μ "]" => entropy X μ

theorem entropy_def (X : Ω → S) (μ : Measure Ω) : H[X ; μ] = Hm[μ.map X] := rfl

theorem entropy_nonneg (X : Ω → S) (μ : Measure Ω) : 0 ≤ H[X ; μ] := measureEntropy_nonneg _

@[simp] theorem entropy_zero_measure (X : Ω → S) : H[X ; (0 : Measure Ω)] = 0 := by
  simp [entropy]

theorem entropy_le_log_card [Fintype S] [MeasurableSingletonClass S] (X : Ω → S)
    (μ : Measure Ω) : H[X ; μ] ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card _

theorem entropy_eq_sum [Fintype S] [MeasurableSingletonClass S] (hX : Measurable X)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] :
    H[X ; μ] = ∑ s, negMulLog (μ.real (X ⁻¹' {s})) := by
  rw [entropy, measureEntropy_eq_sum]
  simp_rw [map_measureReal_apply hX (.singleton _)]

/-- Conditional entropy: the expectation, under the law of `Y`, of the entropy of `X`
conditioned on `Y = y`. -/
noncomputable def condEntropy (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  ∫ y, H[X ; μ[|Y ⁻¹' {y}]] ∂(μ.map Y)

@[inherit_doc condEntropy]
scoped notation3:max "H[" X " | " Y " ; " μ "]" => condEntropy X Y μ

theorem condEntropy_nonneg (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : 0 ≤ H[X | Y ; μ] :=
  integral_nonneg fun _ => entropy_nonneg _ _

theorem condEntropy_eq_sum [Fintype T] [MeasurableSingletonClass T] (X : Ω → S)
    (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] :
    H[X | Y ; μ] = ∑ y, μ.real (Y ⁻¹' {y}) * H[X ; μ[|Y ⁻¹' {y}]] := by
  rw [condEntropy, integral_fintype .of_finite]
  simp_rw [smul_eq_mul, map_measureReal_apply hY (.singleton _)]

/-- Mutual information of two random variables. -/
noncomputable def mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[fun ω => (X ω, Y ω) ; μ]

@[inherit_doc mutualInfo]
scoped notation3:max "I[" X " : " Y " ; " μ "]" => mutualInfo X Y μ

theorem mutualInfo_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[fun ω => (X ω, Y ω) ; μ] := rfl

/-- The mutual information of two random variables is that of their joint law. -/
theorem mutualInfo_eq_measureMutualInfo (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) : I[X : Y ; μ] = Im[μ.map fun ω => (X ω, Y ω)] := by
  rw [mutualInfo, measureMutualInfo, Measure.fst_map_prodMk hY, Measure.snd_map_prodMk hX]
  rfl

variable [Fintype S] [Fintype T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsProbabilityMeasure μ]
include hX hY

theorem mutualInfo_nonneg : 0 ≤ I[X : Y ; μ] := by
  have : IsProbabilityMeasure (μ.map fun ω => (X ω, Y ω)) :=
    ⟨by rw [Measure.map_apply (hX.prodMk hY) .univ, Set.preimage_univ, measure_univ]⟩
  rw [mutualInfo_eq_measureMutualInfo hX hY]
  exact measureMutualInfo_nonneg _

/-- **Chain rule**: `H[X, Y] = H[Y] + H[X | Y]`. -/
theorem chain_rule : H[fun ω => (X ω, Y ω) ; μ] = H[Y ; μ] + H[X | Y ; μ] := by
  have hfib (x : S) (y : T) :
      Y ⁻¹' {y} ∩ X ⁻¹' {x} = (fun ω => (X ω, Y ω)) ⁻¹' {(x, y)} := by
    ext ω; simp [and_comm]
  have hcond (x : S) (y : T) : (μ[|Y ⁻¹' {y}]).real (X ⁻¹' {x})
      = μ.real ((fun ω => (X ω, Y ω)) ⁻¹' {(x, y)}) / μ.real (Y ⁻¹' {y}) := by
    rw [measureReal_def, cond_apply (hY (.singleton y)), ENNReal.toReal_mul,
      ENNReal.toReal_inv, hfib, div_eq_inv_mul]
    rfl
  have hsum (y : T) :
      ∑ x, μ.real ((fun ω => (X ω, Y ω)) ⁻¹' {(x, y)}) = μ.real (Y ⁻¹' {y}) := by
    simp_rw [← map_measureReal_apply (hX.prodMk hY) (.singleton _),
      ← Measure.snd_real_singleton_eq_sum, Measure.snd_map_prodMk hX,
      map_measureReal_apply hY (.singleton _)]
  have key (y : T) : μ.real (Y ⁻¹' {y}) * H[X ; μ[|Y ⁻¹' {y}]]
      = ∑ x, negMulLog (μ.real ((fun ω => (X ω, Y ω)) ⁻¹' {(x, y)}))
        - negMulLog (μ.real (Y ⁻¹' {y})) := by
    obtain hy | hy := eq_or_ne (μ (Y ⁻¹' {y})) 0
    · have h0 (x : S) : μ ((fun ω => (X ω, Y ω)) ⁻¹' {(x, y)}) = 0 :=
        measure_mono_null (hfib x y ▸ Set.inter_subset_left) hy
      simp [cond_eq_zero_of_meas_eq_zero hy, measureReal_def, hy, h0]
    · have := cond_isProbabilityMeasure (μ := μ) hy
      have hq : μ.real (Y ⁻¹' {y}) ≠ 0 :=
        (measureReal_eq_zero_iff (measure_ne_top _ _)).not.mpr hy
      have h (x : S) : μ.real (Y ⁻¹' {y})
            * negMulLog (μ.real ((fun ω => (X ω, Y ω)) ⁻¹' {(x, y)}) / μ.real (Y ⁻¹' {y}))
          = negMulLog (μ.real ((fun ω => (X ω, Y ω)) ⁻¹' {(x, y)}))
            - μ.real ((fun ω => (X ω, Y ω)) ⁻¹' {(x, y)}) / μ.real (Y ⁻¹' {y})
              * negMulLog (μ.real (Y ⁻¹' {y})) := by
        rw [eq_sub_iff_add_eq, add_comm, ← negMulLog_mul]
        congr 1
        field_simp
      rw [entropy_eq_sum hX, Finset.mul_sum]
      simp_rw [hcond, h, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, hsum,
        div_self hq, one_mul]
  rw [entropy_eq_sum (hX.prodMk hY), entropy_eq_sum hY, condEntropy_eq_sum X hY]
  simp_rw [key, Finset.sum_sub_distrib, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  ring

theorem mutualInfo_eq_entropy_sub_condEntropy : I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInfo, chain_rule hX hY]
  ring

/-- Conditioning reduces entropy: `H[X | Y] ≤ H[X]`. -/
theorem condEntropy_le_entropy : H[X | Y ; μ] ≤ H[X ; μ] :=
  sub_nonneg.mp (mutualInfo_eq_entropy_sub_condEntropy hX hY μ ▸ mutualInfo_nonneg hX hY μ)

end entropy

end InformationTheory
