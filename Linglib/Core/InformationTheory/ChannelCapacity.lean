/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy
public import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Core.Probability.Kernel.Posterior
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Channel capacity

A channel from inputs `C` to outputs `W` is a Markov kernel `κ : Kernel C W`. An input
distribution `μ` induces the joint law `μ ⊗ₘ κ` and the output marginal `κ ∘ₘ μ`, and the
capacity of the channel is the supremum over input distributions of the mutual information
`Im[μ ⊗ₘ κ]`.

Over finite alphabets the mutual information is the input average of the divergence of each row
`κ c` from the output marginal, and averaging the divergence from any other reference measure
overshoots it by the divergence of the output marginal from that reference (the compensation
identity). The divergences of the rows characterize the input distributions that attain
capacity, as in the Kuhn–Tucker conditions: an input distribution achieves capacity when no row
lies farther from its output marginal than the information it conveys, and an input distribution
of positive mass everywhere that achieves capacity puts every row at divergence exactly the
capacity from its output marginal.

## Main definitions

* `InformationTheory.channelCapacity`: `⨆ μ, Im[μ ⊗ₘ κ]` over probability measures `μ`.

## Main results

* `InformationTheory.measureMutualInfo_compProd`: `Im[μ ⊗ₘ κ]` is the `μ`-average of the
  divergences `klDiv (κ c) (κ ∘ₘ μ)`.
* `InformationTheory.sum_mul_toReal_klDiv`: the compensation identity.
* `InformationTheory.channelCapacity_le_log_card`: the capacity is at most `log |W|`.
* `InformationTheory.measureMutualInfo_compProd_eq_channelCapacity`: sufficiency of the
  divergence condition.
* `InformationTheory.toReal_klDiv_eq_channelCapacity`: its necessity at an input distribution of
  positive mass everywhere.

## References

* [C. E. Shannon, *A Mathematical Theory of Communication* (1948)][shannon-1948]
* [T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2006)][cover-thomas-2006]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

variable {C W : Type*} [MeasurableSpace C] [MeasurableSpace W] [Fintype C] [Fintype W]
  [MeasurableSingletonClass C] [MeasurableSingletonClass W]

/-- The capacity of a channel: the supremum over input distributions of the mutual information
between its input and output. -/
noncomputable def channelCapacity (κ : Kernel C W) : ℝ :=
  ⨆ μ : ProbabilityMeasure C, Im[(μ : Measure C) ⊗ₘ κ]

variable (κ : Kernel C W) [IsMarkovKernel κ] (μ : Measure C) [IsProbabilityMeasure μ]

private theorem measureMutualInfo_compProd_eq_sum :
    Im[μ ⊗ₘ κ] = ∑ c, μ.real {c} * ∑ w, (κ c).real {w}
      * log ((κ c).real {w} / (κ ∘ₘ μ).real {w}) := by
  rw [measureMutualInfo_eq_toReal_klDiv,
    toReal_klDiv_eq_sum_log_div (Measure.absolutelyContinuous_fst_prod_snd _),
    Measure.fst_compProd, Measure.snd_compProd, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Measure.compProd_real_singleton, Measure.prod_real_singleton]
  obtain hc | hc := eq_or_ne (μ.real {c}) 0
  · simp [hc]
  · rw [mul_div_mul_left _ _ hc, mul_assoc]

omit [IsMarkovKernel κ] [IsProbabilityMeasure μ] in
private theorem comp_absolutelyContinuous {q : Measure W} (hq : ∀ c, μ {c} ≠ 0 → κ c ≪ q) :
    κ ∘ₘ μ ≪ q :=
  Measure.absolutelyContinuous_of_forall_singleton fun w hw => by
    rw [Measure.comp_apply_singleton]
    refine Finset.sum_eq_zero fun c _ => ?_
    obtain hc | hc := eq_or_ne (μ {c}) 0
    · rw [hc, zero_mul]
    · rw [hq c hc hw, mul_zero]

/-- The compensation identity: averaging the divergence of the rows of a channel from a
reference measure overshoots the mutual information by the divergence of the output marginal
from that reference. -/
theorem sum_mul_toReal_klDiv (q : Measure W) [IsProbabilityMeasure q]
    (hq : ∀ c, μ {c} ≠ 0 → κ c ≪ q) :
    ∑ c, μ.real {c} * (klDiv (κ c) q).toReal = Im[μ ⊗ₘ κ] + (klDiv (κ ∘ₘ μ) q).toReal := by
  have key (c : C) (w : W) :
      μ.real {c} * ((κ c).real {w} * log ((κ c).real {w} / q.real {w}))
        = μ.real {c} * ((κ c).real {w} * log ((κ c).real {w} / (κ ∘ₘ μ).real {w}))
          + μ.real {c} * (κ c).real {w} * log ((κ ∘ₘ μ).real {w} / q.real {w}) := by
    obtain h0 | h0 := eq_or_ne (μ.real {c} * (κ c).real {w}) 0
    · rcases mul_eq_zero.mp h0 with h | h <;> simp [h]
    obtain ⟨hc, hk⟩ := mul_ne_zero_iff.mp h0
    have hq : q.real {w} ≠ 0 := by
      rw [Ne, measureReal_eq_zero_iff (measure_ne_top _ _)] at hc hk ⊢
      exact fun h => hk (hq c hc h)
    have hr : (κ ∘ₘ μ).real {w} ≠ 0 := by
      refine (lt_of_lt_of_le (lt_of_le_of_ne (by positivity) (Ne.symm h0)) ?_).ne'
      rw [Measure.comp_real_singleton]
      exact Finset.single_le_sum (f := fun c => μ.real {c} * (κ c).real {w})
        (fun _ _ => by positivity) (Finset.mem_univ c)
    rw [← div_mul_div_cancel₀ hr, log_mul (div_ne_zero hk hr) (div_ne_zero hr hq)]
    ring
  rw [measureMutualInfo_compProd_eq_sum,
    toReal_klDiv_eq_sum_log_div (comp_absolutelyContinuous κ μ hq)]
  calc ∑ c, μ.real {c} * (klDiv (κ c) q).toReal
      = ∑ c, ∑ w, μ.real {c} * ((κ c).real {w} * log ((κ c).real {w} / q.real {w})) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        obtain hc | hc := eq_or_ne (μ {c}) 0
        · simp [measureReal_def, hc]
        · rw [toReal_klDiv_eq_sum_log_div (hq c hc), Finset.mul_sum]
    _ = _ := by
        simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_comm (f := fun c w => μ.real {c} * (κ c).real {w}
          * log ((κ ∘ₘ μ).real {w} / q.real {w}))]
        simp_rw [← Finset.sum_mul, ← Measure.comp_real_singleton]

/-- Mutual information across a channel is the input average of the divergence of each row from
the output marginal. -/
theorem measureMutualInfo_compProd :
    Im[μ ⊗ₘ κ] = ∑ c, μ.real {c} * (klDiv (κ c) (κ ∘ₘ μ)).toReal := by
  rw [sum_mul_toReal_klDiv κ μ _ fun c hc => κ.absolutelyContinuous_comp μ hc, klDiv_self,
    ENNReal.toReal_zero, add_zero]

/-- Mutual information across a channel is at most the log of the number of outputs. -/
theorem measureMutualInfo_compProd_le_log_card : Im[μ ⊗ₘ κ] ≤ log (Fintype.card W) :=
  (measureMutualInfo_le_measureEntropy_snd _).trans (measureEntropy_le_log_card _)

/-- The capacity of a channel is at most the log of the number of outputs. -/
theorem channelCapacity_le_log_card : channelCapacity κ ≤ log (Fintype.card W) :=
  Real.iSup_le (fun μ => measureMutualInfo_compProd_le_log_card κ μ) (log_natCast_nonneg _)

theorem channelCapacity_nonneg : 0 ≤ channelCapacity κ :=
  Real.iSup_nonneg fun _ => measureMutualInfo_nonneg _

theorem measureMutualInfo_compProd_le_channelCapacity : Im[μ ⊗ₘ κ] ≤ channelCapacity κ :=
  le_ciSup (f := fun μ : ProbabilityMeasure C => Im[(μ : Measure C) ⊗ₘ κ])
    ⟨log (Fintype.card W), by
      rintro _ ⟨μ, rfl⟩
      exact measureMutualInfo_compProd_le_log_card κ μ⟩ ⟨μ, inferInstance⟩

/-- **Sufficiency of the divergence condition.** An input distribution achieves capacity when no
row of the channel lies farther from the output marginal than the information conveyed. -/
theorem measureMutualInfo_compProd_eq_channelCapacity
    (h : ∀ c, klDiv (κ c) (κ ∘ₘ μ) ≤ ENNReal.ofReal (Im[μ ⊗ₘ κ])) :
    Im[μ ⊗ₘ κ] = channelCapacity κ := by
  refine le_antisymm (measureMutualInfo_compProd_le_channelCapacity κ μ)
    (Real.iSup_le (fun ν => ?_) (measureMutualInfo_nonneg _))
  have hac (c : C) : κ c ≪ κ ∘ₘ μ := by
    by_contra hc
    exact ENNReal.ofReal_ne_top (top_le_iff.mp (klDiv_eq_top_iff_not_ac.mpr hc ▸ h c))
  calc Im[(ν : Measure C) ⊗ₘ κ]
      ≤ ∑ c, (ν : Measure C).real {c} * (klDiv (κ c) (κ ∘ₘ μ)).toReal := by
        rw [sum_mul_toReal_klDiv κ ν (κ ∘ₘ μ) fun c _ => hac c]
        exact le_add_of_nonneg_right ENNReal.toReal_nonneg
    _ ≤ ∑ c, (ν : Measure C).real {c} * Im[μ ⊗ₘ κ] :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
          (ENNReal.toReal_le_of_le_ofReal (measureMutualInfo_nonneg _) (h c)) measureReal_nonneg
    _ = Im[μ ⊗ₘ κ] := by
        rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

/-- At a capacity-achieving input distribution of positive mass everywhere, no row lies farther
from the output marginal than the capacity: moving mass `t` onto one input raises the mutual
information by `t` times the excess of that row's divergence, less a divergence of order `t²`. -/
private theorem toReal_klDiv_le (hμ : ∀ c, μ {c} ≠ 0) (h : Im[μ ⊗ₘ κ] = channelCapacity κ)
    (c : C) : (klDiv (κ c) (κ ∘ₘ μ)).toReal ≤ Im[μ ⊗ₘ κ] := by
  have hac (c' : C) : κ c' ≪ κ ∘ₘ μ := κ.absolutelyContinuous_comp μ (hμ c')
  set A := ∑ w, (κ c).real {w} ^ 2 / (κ ∘ₘ μ).real {w} - 1
  have key (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
      t * ((klDiv (κ c) (κ ∘ₘ μ)).toReal - Im[μ ⊗ₘ κ]) ≤ t ^ 2 * A := by
    classical
    set ν : Measure C := ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • Measure.dirac c
    have hν (c' : C) : ν.real {c'} = (1 - t) * μ.real {c'} + t * if c = c' then 1 else 0 := by
      simp only [ν, measureReal_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply' c (measurableSet_singleton c'), Set.indicator_apply,
        Set.mem_singleton_iff, Pi.one_apply]
      rw [ENNReal.toReal_add (by finiteness) (by split_ifs <;> simp), ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal ht0.le]
      split_ifs <;> simp
    have : IsProbabilityMeasure ν := ⟨by
      simp only [ν, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
      rw [← ENNReal.ofReal_add (by linarith) ht0.le, sub_add_cancel, ENNReal.ofReal_one]⟩
    have hq (w : W) :
        (κ ∘ₘ ν).real {w} = (1 - t) * (κ ∘ₘ μ).real {w} + t * (κ c).real {w} := by
      simp_rw [Measure.comp_real_singleton, hν, add_mul, Finset.sum_add_distrib, mul_assoc,
        ← Finset.mul_sum, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true]
    have hlhs : ∑ c', ν.real {c'} * (klDiv (κ c') (κ ∘ₘ μ)).toReal
        = (1 - t) * Im[μ ⊗ₘ κ] + t * (klDiv (κ c) (κ ∘ₘ μ)).toReal := by
      simp_rw [hν, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
        ← measureMutualInfo_compProd κ μ, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    have hsq (w : W) : ((1 - t) * (κ ∘ₘ μ).real {w} + t * (κ c).real {w}) ^ 2 / (κ ∘ₘ μ).real {w}
        = (1 - t) ^ 2 * (κ ∘ₘ μ).real {w} + 2 * t * (1 - t) * (κ c).real {w}
          + t ^ 2 * ((κ c).real {w} ^ 2 / (κ ∘ₘ μ).real {w}) := by
      obtain hw | hw := eq_or_ne ((κ ∘ₘ μ).real {w}) 0
      · have hk : (κ c).real {w} = 0 := by
          rw [measureReal_eq_zero_iff (measure_ne_top _ _)] at hw ⊢
          exact hac c hw
        simp [hw, hk]
      · field_simp
        ring
    have hKL : (klDiv (κ ∘ₘ ν) (κ ∘ₘ μ)).toReal ≤ t ^ 2 * A := by
      have hνac : κ ∘ₘ ν ≪ κ ∘ₘ μ := comp_absolutelyContinuous κ ν fun c' _ => hac c'
      rw [toReal_klDiv_eq_sum_log_div hνac]
      calc ∑ w, (κ ∘ₘ ν).real {w} * log ((κ ∘ₘ ν).real {w} / (κ ∘ₘ μ).real {w})
          ≤ ∑ w, ((κ ∘ₘ ν).real {w} ^ 2 / (κ ∘ₘ μ).real {w} - (κ ∘ₘ ν).real {w}) := by
            refine Finset.sum_le_sum fun w _ => ?_
            obtain hx | hx := eq_or_ne ((κ ∘ₘ ν).real {w}) 0
            · simp [hx]
            have hy : (κ ∘ₘ μ).real {w} ≠ 0 := by
              rw [Ne, measureReal_eq_zero_iff (measure_ne_top _ _)] at hx ⊢
              exact fun h => hx (hνac h)
            have hxpos := lt_of_le_of_ne measureReal_nonneg (Ne.symm hx)
            have hypos := lt_of_le_of_ne measureReal_nonneg (Ne.symm hy)
            calc (κ ∘ₘ ν).real {w} * log ((κ ∘ₘ ν).real {w} / (κ ∘ₘ μ).real {w})
                ≤ (κ ∘ₘ ν).real {w} * ((κ ∘ₘ ν).real {w} / (κ ∘ₘ μ).real {w} - 1) :=
                  mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hxpos hypos))
                    hxpos.le
              _ = _ := by ring
        _ = t ^ 2 * A := by
            rw [Finset.sum_sub_distrib, sum_measureReal_singleton_eq_one]
            simp_rw [hq, hsq, Finset.sum_add_distrib, ← Finset.mul_sum,
              sum_measureReal_singleton_eq_one]
            ring
    have hcomp := sum_mul_toReal_klDiv κ ν (κ ∘ₘ μ) fun c' _ => hac c'
    have hcap : Im[ν ⊗ₘ κ] ≤ Im[μ ⊗ₘ κ] := h ▸ measureMutualInfo_compProd_le_channelCapacity κ ν
    linarith
  by_contra hlt
  set ε := (klDiv (κ c) (κ ∘ₘ μ)).toReal - Im[μ ⊗ₘ κ]
  have hε : 0 < ε := sub_pos.mpr (not_le.mp hlt)
  set t := min 1 (ε / (2 * (|A| + 1)))
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have htA : t * A < ε := calc
    t * A ≤ ε / (2 * (|A| + 1)) * |A| :=
      (mul_le_mul_of_nonneg_left (le_abs_self A) ht0.le).trans
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg A))
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg A]
  have := key t ht0 (min_le_left _ _)
  have : ε ≤ t * A := le_of_mul_le_mul_left (by nlinarith) ht0
  linarith

/-- **Necessity of the divergence condition.** An input distribution of positive mass everywhere
that achieves capacity puts every row of the channel at divergence exactly the capacity from the
output marginal. -/
theorem toReal_klDiv_eq_channelCapacity (hμ : ∀ c, μ {c} ≠ 0)
    (h : Im[μ ⊗ₘ κ] = channelCapacity κ) (c : C) :
    (klDiv (κ c) (κ ∘ₘ μ)).toReal = channelCapacity κ := by
  rw [← h]
  refine (toReal_klDiv_le κ μ hμ h c).eq_of_not_lt fun hlt => ?_
  have hpos : 0 < μ.real {c} := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hμ c) (measure_ne_top _ _)
  have := Finset.sum_lt_sum (s := Finset.univ)
    (fun c' _ => mul_le_mul_of_nonneg_left (toReal_klDiv_le κ μ hμ h c') measureReal_nonneg)
    ⟨c, Finset.mem_univ c, mul_lt_mul_of_pos_left hlt hpos⟩
  rw [← measureMutualInfo_compProd, ← Finset.sum_mul, sum_measureReal_singleton_eq_one,
    one_mul] at this
  exact lt_irrefl _ this

end InformationTheory
