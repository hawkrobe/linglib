/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.InformationTheory.Surprisal
public import Linglib.Core.Probability.AutoregressiveSequenceModel
public import Linglib.Core.Probability.Kernel.OfWeights

/-!
# Cotterell (2026): Surprisal Theory is Tautological (without Rational Grounding)

Surprisal theory holds that the processing difficulty of a unit in context is an affine function
of its surprisal under some language model, with a positive slope and a baseline that may depend
on the context. [cotterell-2026] argues that the claim is a tautology unless the language model is
constrained: any nonnegative difficulty measure `d` over the next unit, or the end of the string,
given a prefix, defines the model whose next-unit distribution is the softmax of `-d`, and its
surprisal is `d` plus the log partition function of the prefix (`surprisal_softmaxModel`), so
the claim holds with slope one and the negative log partition function as baseline. The one
condition is that the model be a language model, i.e. tight. When the end difficulty is bounded
along a series whose exponentials diverge, the softmax model ends with probability at least those
exponentials over the size of the extended alphabet, and it is tight by [du-etal-2023]'s
sufficient condition (`isTight_softmaxModel`), which gives the tautology
(`exists_isTight_difficulty_eq_surprisal`); a constant bound also gives it finite expected length
(`tsum_length_mul_stringProb_softmaxModel_ne_top`). Without the bound the construction can fail:
an end difficulty growing linearly in the length of the prefix leaves the softmax model non-tight
(`not_isTight_softmaxModel_length`).

## Implementation notes

* The difficulty measure takes the next unit before the prefix, `d o u` for `d(o | u)`, with
  `none` for the end of the string.
* The divergence hypothesis is stated in `ℝ≥0∞`, where a sum of nonnegative terms equals `∞`
  exactly when the series diverges; the paper states it for real series.
* The paper's bound `f` is nonnegative and its constant bound positive; neither sign condition is
  needed here.
* The paper remarks that the softmax construction need not give a language model but gives no
  example; `not_isTight_softmaxModel_length` is an added witness.
* The paper's fitness measure, its consistency theorem for maximum-likelihood estimation, and its
  scaling implication are not formalized.

## References

* [cotterell-2026]
* [du-etal-2023]
-/

@[expose] public section

namespace Cotterell2026

open InformationTheory MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The model whose next-unit distribution after `u` is proportional to `exp (-d o u)`. -/
noncomputable def softmaxModel (d : Option α → List α → ℝ) : AutoregressiveSequenceModel α where
  next := Kernel.ofWeights fun u o ↦ ENNReal.ofReal (exp (-d o u))
  isMarkovKernel_next := Kernel.isMarkovKernel_ofWeights
    (fun _ ↦ ⟨none, (ENNReal.ofReal_pos.2 (exp_pos _)).ne'⟩) fun _ _ ↦ ENNReal.ofReal_ne_top

variable (d : Option α → List α → ℝ)

theorem real_next_softmaxModel (u : List α) (o : Option α) :
    ((softmaxModel d).next u).real {o} = softmax (fun o ↦ -d o u) o := by
  rw [softmaxModel, Kernel.ofWeights_real_singleton _ _ fun _ ↦ ENNReal.ofReal_ne_top,
    softmax_def]
  simp only [ENNReal.toReal_ofReal (exp_pos _).le]

/-- The surprisal of the softmax model is the difficulty plus the log partition function of the
prefix. -/
theorem surprisal_softmaxModel (u : List α) (o : Option α) :
    surprisal ((softmaxModel d).next u) o = d o u + log (∑ o', exp (-d o' u)) := by
  rw [surprisal, real_next_softmaxModel, log_softmax]
  ring

variable {d}

/-- A nonnegative difficulty measure makes the softmax model end with probability at least
`exp (-d none u)` over the size of the extended alphabet. -/
theorem le_next_none_softmaxModel (hd : ∀ o u, 0 ≤ d o u) (u : List α) :
    ENNReal.ofReal (exp (-d none u)) / Fintype.card (Option α) ≤
      (softmaxModel d).next u {none} := by
  rw [softmaxModel, Kernel.ofWeights_apply_singleton]
  refine ENNReal.div_le_div le_rfl ?_
  calc ∑ o, ENNReal.ofReal (exp (-d o u)) ≤ ∑ _o : Option α, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun o _ ↦
          ENNReal.ofReal_le_one.2 (exp_le_one_iff.2 (by linarith [hd o u]))
    _ = Fintype.card (Option α) := by simp

/-- Proposition 1(a): a nonnegative difficulty measure whose end difficulty after a prefix of
length `t - 1` is at most `f t`, with `∑ exp (-f t)` divergent, gives a tight softmax model. -/
theorem isTight_softmaxModel (hd : ∀ o u, 0 ≤ d o u) {f : ℕ → ℝ}
    (hf : ∀ u, d none u ≤ f (u.length + 1)) (hdiv : ∑' t, ENNReal.ofReal (exp (-f (t + 1))) = ∞) :
    (softmaxModel d).IsTight := by
  refine (softmaxModel d).isTight_of_le_next_none
    (f := fun t ↦ ENNReal.ofReal (exp (-f t)) / Fintype.card (Option α)) (fun u ↦ ?_) ?_
  · refine le_trans ?_ (le_next_none_softmaxModel hd u)
    gcongr
    exact hf u
  · simp only [div_eq_mul_inv, ENNReal.tsum_mul_right, hdiv]
    exact ENNReal.top_mul (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))

/-- The softmax model need not be a language model: an end difficulty growing linearly in the
length of the prefix, with every other difficulty zero, leaves it non-tight. -/
theorem not_isTight_softmaxModel_length [Nonempty α] :
    ¬ (softmaxModel fun (o : Option α) u ↦ o.elim ((u.length : ℝ) + 1) fun _ ↦ 0).IsTight := by
  set w : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (exp (-((n : ℝ) + 1)))
  have hk : (Fintype.card α : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hw (n : ℕ) : w n ≠ ∞ := ENNReal.ofReal_ne_top
  rw [(softmaxModel _).isTight_iff_of_next_none_eq (e := fun n ↦ w n / (w n + Fintype.card α))
    (fun x ↦ by simp [softmaxModel, Kernel.ofWeights_apply_singleton, Fintype.sum_option, w])
    fun n ↦ ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_self_add)]
  rintro (⟨n, hn⟩ | hsum)
  · rw [ENNReal.div_eq_one_iff (by simp [hk]) (by simp [hw n])] at hn
    exact hk ((ENNReal.add_right_inj (hw n)).1 (hn.symm.trans (add_zero _).symm))
  · have hle (n : ℕ) : w n / (w n + Fintype.card α) ≤ w n :=
      ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' ((Nat.one_le_cast.2 Fintype.card_pos).trans
        le_add_self))
    have hr : ENNReal.ofReal (exp (-1)) < 1 :=
      ENNReal.ofReal_lt_one.2 (exp_lt_one_iff.2 (by norm_num))
    have hpow (n : ℕ) : w n = ENNReal.ofReal (exp (-1)) ^ (n + 1) := by
      simp only [w, ← ENNReal.ofReal_pow (exp_pos _).le, ← exp_nat_mul]
      congr 2; push_cast; ring
    refine ((ENNReal.tsum_le_tsum hle).trans_lt ?_).ne hsum
    calc ∑' n, w n = ∑' n : ℕ, ENNReal.ofReal (exp (-1)) ^ (n + 1) := tsum_congr hpow
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (exp (-1)) ^ n :=
        ENNReal.tsum_le_tsum fun n ↦ pow_le_pow_of_le_one bot_le hr.le n.le_succ
      _ < ∞ := by rw [ENNReal.tsum_geometric]; exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr)

/-- The tautology: a nonnegative difficulty measure whose end difficulty is bounded along a
series with divergent exponentials is the surprisal of some language model up to a
context-dependent baseline. -/
theorem exists_isTight_difficulty_eq_surprisal (hd : ∀ o u, 0 ≤ d o u) {f : ℕ → ℝ}
    (hf : ∀ u, d none u ≤ f (u.length + 1)) (hdiv : ∑' t, ENNReal.ofReal (exp (-f (t + 1))) = ∞) :
    ∃ M : AutoregressiveSequenceModel α, M.IsTight ∧
      ∃ b : List α → ℝ, ∀ o u, d o u = surprisal (M.next u) o + b u :=
  ⟨softmaxModel d, isTight_softmaxModel hd hf hdiv, fun u ↦ -log (∑ o', exp (-d o' u)),
    fun o u ↦ by rw [surprisal_softmaxModel]; ring⟩

/-- Proposition 1(b): a constant bound on the end difficulty gives the softmax model finite
expected length. -/
theorem tsum_length_mul_stringProb_softmaxModel_ne_top (hd : ∀ o u, 0 ≤ d o u) {C : ℝ}
    (hC : ∀ u, d none u ≤ C) :
    ∑' x, (x.length : ℝ≥0∞) * (softmaxModel d).stringProb x ≠ ∞ := by
  set c : ℝ≥0∞ := ENNReal.ofReal (exp (-C)) / Fintype.card (Option α)
  have hc (u : List α) : c ≤ (softmaxModel d).next u {none} := by
    refine le_trans ?_ (le_next_none_softmaxModel hd u)
    simp only [c]
    gcongr
    exact hC u
  have hc0 : c ≠ 0 := ENNReal.div_ne_zero.2 ⟨(ENNReal.ofReal_pos.2 (exp_pos _)).ne',
    ENNReal.natCast_ne_top _⟩
  have hc1 : c ≤ 1 := (hc []).trans prob_le_one
  refine ne_top_of_le_ne_top ?_ ((softmaxModel d).tsum_length_mul_stringProb_le.trans
    (ENNReal.tsum_le_tsum fun n ↦ ((softmaxModel d).survival_le_pow hc (n + 1)).trans
      (pow_le_pow_of_le_one bot_le tsub_le_self n.le_succ)))
  rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top hc1]
  exact ENNReal.inv_ne_top.2 hc0

end Cotterell2026
