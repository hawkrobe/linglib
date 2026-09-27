/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecificLimits.ProdOneSub
public import Linglib.Core.MeasureTheory.Constructions.List
public import Linglib.Core.MeasureTheory.Constructions.Option
public import Mathlib.Probability.Kernel.Basic

/-!
# Autoregressive sequence models

An autoregressive sequence model over an alphabet `α` gives, after every prefix, a distribution
over the next symbol or the end of the string, `none` [du-etal-2023]. The prefix probability of a
string is the product of the conditional probabilities along it, and the probability of the
string itself multiplies in the probability of ending after it. The string probabilities need not
sum to one: the remaining mass leaks to sequences that never end. A model is tight when they do.

Tightness is a statement about survival, the probability that no end symbol appears in the first
`n` steps. The probabilities of the strings shorter than `n` and the survival at `n` sum to one,
so a model is tight exactly when survival tends to zero. Survival is the product of one minus the
end probability at each step given survival to it, so a model is tight exactly when that
conditional end probability reaches one or has a divergent sum; an end probability bounded below
by a divergent series suffices.

## Main definitions

* `AutoregressiveSequenceModel α`: a Markov kernel from prefixes to `Option α`.
* `condPrefixProb`, `prefixProb`, `stringProb`, `stringMeasure`.
* `IsTight`: the string probabilities sum to one.
* `survival`, `stopProb`, `eosHazard`.

## Main results

* `condPrefixProb_append`: the chain rule for prefix probabilities.
* `sum_range_stopProb_add_survival`, `isTight_iff_tendsto_survival`.
* `survival_eq_prod`: survival is a product over the conditional end probabilities.
* `isTight_iff`: tight exactly when the conditional end probability reaches one or has a
  divergent sum ([du-etal-2023], Theorem 4.7).
* `isTight_of_le_next_none`: a divergent lower bound on the end probability gives tightness
  ([du-etal-2023], Proposition 4.3).
* `survival_le_pow`: a constant lower bound makes survival decay geometrically.
* `isTight_iff_of_next_none_eq`: the criterion when the end probability depends only on length.
* `tsum_length_mul_stringProb_le`: expected length is at most total survival.

## Implementation notes

* The alphabet need only be countable with measurable singletons; [du-etal-2023] take it finite.
* The product criterion behind `isTight_iff` is `ENNReal.tendsto_prod_range_one_sub_nhds_zero_iff`,
  [du-etal-2023]'s Corollary 4.6 extended to factors that may vanish.
* [du-etal-2023] count steps from one, so their conditional end probability at step `t` is
  `eosHazard (t - 1)`. Where survival is zero the ratio is `0` by the convention of `ℝ≥0∞`
  division; the characterization is unaffected, since survival first reaching zero forces a
  conditional end probability of one.
* [du-etal-2023] define tightness through a measure on finite and infinite sequences as zero mass
  on the infinite ones, and show it equivalent to the string probabilities summing to one, which
  is the definition here.

## References

* [du-etal-2023]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Topology
open scoped ENNReal

/-- An autoregressive sequence model over the alphabet `α`: after each prefix, a distribution over
the next symbol, or the end of the string, `none`. -/
structure AutoregressiveSequenceModel (α : Type*) [MeasurableSpace α] where
  /-- The distribution of what follows a prefix. -/
  next : Kernel (List α) (Option α)
  [isMarkovKernel_next : IsMarkovKernel next]

namespace AutoregressiveSequenceModel

attribute [instance] isMarkovKernel_next

variable {α : Type*} [MeasurableSpace α] (M : AutoregressiveSequenceModel α)

/-! ### Prefix and string probabilities -/

/-- The probability that the continuation of the context `c` begins with `x`: the product of the
conditional probabilities along `x`. -/
noncomputable def condPrefixProb : List α → List α → ℝ≥0∞
  | _, [] => 1
  | c, a :: x => M.next c {some a} * condPrefixProb (c ++ [a]) x

@[simp] theorem condPrefixProb_nil (c : List α) : M.condPrefixProb c [] = 1 := rfl

@[simp] theorem condPrefixProb_cons (c : List α) (a : α) (x : List α) :
    M.condPrefixProb c (a :: x) = M.next c {some a} * M.condPrefixProb (c ++ [a]) x := rfl

/-- The chain rule: a continuation begins with `x ++ y` when it begins with `x` and the
continuation of `c ++ x` begins with `y`. -/
theorem condPrefixProb_append (c x y : List α) :
    M.condPrefixProb c (x ++ y) = M.condPrefixProb c x * M.condPrefixProb (c ++ x) y := by
  induction x generalizing c with
  | nil => simp
  | cons a x ih => simp [ih, mul_assoc]

/-- The prefix probability of `x`: the probability that a generated string begins with `x`. -/
noncomputable def prefixProb (x : List α) : ℝ≥0∞ := M.condPrefixProb [] x

@[simp] theorem prefixProb_nil : M.prefixProb [] = 1 := rfl

theorem prefixProb_concat (x : List α) (a : α) :
    M.prefixProb (x ++ [a]) = M.prefixProb x * M.next x {some a} := by
  simp [prefixProb, condPrefixProb_append]

/-- The probability of generating exactly `x`: its prefix probability times the probability of
ending after it. -/
noncomputable def stringProb (x : List α) : ℝ≥0∞ := M.prefixProb x * M.next x {none}

/-- The law of the generated string, carried by the finite strings. -/
noncomputable def stringMeasure : Measure (List α) :=
  Measure.sum fun x ↦ M.stringProb x • Measure.dirac x

@[simp] theorem stringMeasure_singleton (x : List α) : M.stringMeasure {x} = M.stringProb x := by
  classical
  rw [stringMeasure, Measure.sum_apply _ (measurableSet_singleton x)]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton x),
    Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq x _

theorem stringMeasure_univ : M.stringMeasure Set.univ = ∑' x, M.stringProb x := by
  simp [stringMeasure, Measure.sum_apply _ MeasurableSet.univ]

/-- A model is tight when its string probabilities sum to one: no mass leaks to sequences that
never end. -/
def IsTight : Prop := ∑' x, M.stringProb x = 1

theorem isTight_iff_isProbabilityMeasure : M.IsTight ↔ IsProbabilityMeasure M.stringMeasure :=
  ⟨fun h ↦ ⟨by rw [stringMeasure_univ, h]⟩, fun h ↦ by
    rw [IsTight, ← stringMeasure_univ, measure_univ]⟩

/-! ### Survival -/

/-- The probability that no end symbol appears in the first `n` steps: the total prefix
probability of the strings of length `n`. -/
noncomputable def survival (n : ℕ) : ℝ≥0∞ := ∑' x : {x : List α // x.length = n}, M.prefixProb x

/-- The probability of generating a string of length `n`. -/
noncomputable def stopProb (n : ℕ) : ℝ≥0∞ := ∑' x : {x : List α // x.length = n}, M.stringProb x

/-- The probability of ending after `n` symbols given survival to that point, the end
probability at step `n + 1` of [du-etal-2023]. -/
noncomputable def eosHazard (n : ℕ) : ℝ≥0∞ := M.stopProb n / M.survival n

@[simp] theorem survival_zero : M.survival 0 = 1 := by
  rw [survival, tsum_eq_single (⟨[], rfl⟩ : {x : List α // x.length = 0}) fun x hx ↦
    absurd (Subtype.ext (List.eq_nil_of_length_eq_zero x.2)) hx]
  rfl

theorem tsum_stringProb : ∑' x, M.stringProb x = ∑' n, M.stopProb n := by
  rw [← (Equiv.sigmaFiberEquiv List.length).tsum_eq, ENNReal.tsum_sigma']
  rfl

/-- Strings of length `n + 1` are the strings of length `n` followed by a symbol. -/
private def concatEquiv (n : ℕ) :
    {x : List α // x.length = n} × α ≃ {y : List α // y.length = n + 1} where
  toFun p := ⟨p.1.1 ++ [p.2], by simp [p.1.2]⟩
  invFun y := (⟨y.1.dropLast, by simp [y.2]⟩, y.1.getLast (List.ne_nil_of_length_eq_add_one y.2))
  left_inv p := by ext <;> simp
  right_inv y := Subtype.ext (List.dropLast_append_getLast _)

variable [Countable α] [MeasurableSingletonClass α]

/-- After any prefix the model either ends or continues with some symbol. -/
theorem next_none_add_tsum_next_some (x : List α) :
    M.next x {none} + ∑' a, M.next x {some a} = 1 := by
  have hU : ({none} : Set (Option α))ᶜ = ⋃ a, {some a} := by ext o; cases o <;> simp
  rw [← measure_iUnion (fun a b hab ↦ Set.disjoint_singleton.2 ((Option.some_injective α).ne hab))
    fun a ↦ measurableSet_singleton _, ← hU, measure_add_measure_compl (measurableSet_singleton _),
    measure_univ]

theorem survival_succ_add_stopProb (n : ℕ) : M.survival (n + 1) + M.stopProb n = M.survival n := by
  rw [survival, ← (concatEquiv n).tsum_eq, ENNReal.tsum_prod', stopProb, survival,
    ← ENNReal.tsum_add]
  refine tsum_congr fun x ↦ ?_
  simp only [concatEquiv, Equiv.coe_fn_mk, prefixProb_concat, ENNReal.tsum_mul_left, stringProb,
    ← mul_add, add_comm (∑' a, _), next_none_add_tsum_next_some, mul_one]

theorem sum_range_stopProb_add_survival (n : ℕ) :
    ∑ k ∈ range n, M.stopProb k + M.survival n = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_assoc, add_comm (M.stopProb n),
      survival_succ_add_stopProb, ih]

theorem survival_le_one (n : ℕ) : M.survival n ≤ 1 :=
  (M.sum_range_stopProb_add_survival n).le.trans' le_add_self

theorem survival_ne_top (n : ℕ) : M.survival n ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (M.survival_le_one n)

theorem stopProb_le_survival (n : ℕ) : M.stopProb n ≤ M.survival n :=
  (M.survival_succ_add_stopProb n).le.trans' le_add_self

theorem survival_antitone : Antitone M.survival :=
  antitone_nat_of_succ_le fun n ↦ (M.survival_succ_add_stopProb n).le.trans' le_self_add

theorem isTight_iff_tendsto_survival : M.IsTight ↔ Tendsto M.survival atTop (𝓝 0) := by
  have hsum (n : ℕ) : ∑ k ∈ range n, M.stopProb k = 1 - M.survival n :=
    ENNReal.eq_sub_of_add_eq (M.survival_ne_top n) (M.sum_range_stopProb_add_survival n)
  have hinf : ⨅ n, M.survival n ≤ 1 := (iInf_le _ 0).trans (M.survival_le_one 0)
  rw [IsTight, tsum_stringProb, ENNReal.tsum_eq_iSup_nat, iSup_congr hsum, ← ENNReal.sub_iInf]
  constructor
  · intro h
    have h0 : ⨅ n, M.survival n = 0 := by
      rw [← ENNReal.sub_sub_cancel ENNReal.one_ne_top hinf, h, tsub_self]
    exact h0 ▸ tendsto_atTop_iInf M.survival_antitone
  · intro h
    rw [tendsto_nhds_unique (tendsto_atTop_iInf M.survival_antitone) h, tsub_zero]

/-! ### The conditional end probability -/

theorem eosHazard_le_one (n : ℕ) : M.eosHazard n ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact M.stopProb_le_survival n)

theorem survival_succ (n : ℕ) : M.survival (n + 1) = M.survival n * (1 - M.eosHazard n) := by
  by_cases h : M.survival n = 0
  · rw [h, zero_mul]
    exact nonpos_iff_eq_zero.1 ((M.survival_antitone n.le_succ).trans h.le)
  · rw [ENNReal.mul_sub fun _ _ ↦ M.survival_ne_top n, mul_one, eosHazard,
      ENNReal.mul_div_cancel h (M.survival_ne_top n)]
    exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (M.survival_ne_top n)
      (M.stopProb_le_survival n)) (M.survival_succ_add_stopProb n)

theorem survival_eq_prod (n : ℕ) : M.survival n = ∏ k ∈ range n, (1 - M.eosHazard k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [survival_succ, ih, prod_range_succ]

/-- A model is tight exactly when the conditional end probability reaches one or has a divergent
sum ([du-etal-2023], Theorem 4.7). -/
theorem isTight_iff : M.IsTight ↔ (∃ n, M.eosHazard n = 1) ∨ ∑' n, M.eosHazard n = ∞ := by
  rw [isTight_iff_tendsto_survival, funext M.survival_eq_prod]
  exact ENNReal.tendsto_prod_range_one_sub_nhds_zero_iff M.eosHazard_le_one

omit [Countable α] [MeasurableSingletonClass α] in
/-- The strings of length `n` end with probability at least `c` times survival to `n` when every
prefix of length `n` ends with probability at least `c`. -/
theorem mul_survival_le_stopProb {n : ℕ} {c : ℝ≥0∞}
    (hc : ∀ x : List α, x.length = n → c ≤ M.next x {none}) :
    c * M.survival n ≤ M.stopProb n := by
  rw [survival, ← ENNReal.tsum_mul_left, stopProb]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  rw [stringProb, mul_comm c]
  gcongr
  exact hc x x.2

/-- A model whose end probability after every prefix of length `t - 1` is at least `f t`, for a
divergent series of bounds, is tight ([du-etal-2023], Proposition 4.3). -/
theorem isTight_of_le_next_none {f : ℕ → ℝ≥0∞}
    (hf : ∀ x : List α, f (x.length + 1) ≤ M.next x {none}) (h : ∑' t, f (t + 1) = ∞) :
    M.IsTight := by
  by_cases hs : ∃ n, M.survival n = 0
  · obtain ⟨n, hn⟩ := hs
    rw [isTight_iff_tendsto_survival]
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n, fun m hm ↦ ?_⟩)
    exact (nonpos_iff_eq_zero.1 ((M.survival_antitone hm).trans hn.le)).symm
  · simp only [not_exists] at hs
    refine M.isTight_iff.2 (.inr (eq_top_mono (ENNReal.tsum_le_tsum fun n ↦ ?_) h))
    rw [eosHazard, ENNReal.le_div_iff_mul_le (.inl (hs n)) (.inl (M.survival_ne_top n))]
    exact M.mul_survival_le_stopProb fun x hx ↦ hx ▸ hf x

/-- When the end probability after a prefix depends only on its length, survival is the product
of one minus it. -/
theorem survival_eq_prod_of_next_none_eq {e : ℕ → ℝ≥0∞}
    (he : ∀ x : List α, M.next x {none} = e x.length) (n : ℕ) :
    M.survival n = ∏ k ∈ range n, (1 - e k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstop : M.stopProb n = e n * M.survival n := by
      rw [stopProb, survival, ← ENNReal.tsum_mul_left]
      exact tsum_congr fun x ↦ by rw [stringProb, he, x.2, mul_comm]
    rw [prod_range_succ, ← ih, ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (M.survival_ne_top n)
      (M.stopProb_le_survival n)) (M.survival_succ_add_stopProb n), hstop,
      ENNReal.mul_sub fun _ _ ↦ M.survival_ne_top n, mul_one, mul_comm]

/-- When the end probability after a prefix depends only on its length, the model is tight exactly
when that probability reaches one or has a divergent sum. -/
theorem isTight_iff_of_next_none_eq {e : ℕ → ℝ≥0∞}
    (he : ∀ x : List α, M.next x {none} = e x.length) (he1 : ∀ n, e n ≤ 1) :
    M.IsTight ↔ (∃ n, e n = 1) ∨ ∑' n, e n = ∞ := by
  rw [isTight_iff_tendsto_survival, funext (M.survival_eq_prod_of_next_none_eq he)]
  exact ENNReal.tendsto_prod_range_one_sub_nhds_zero_iff he1

/-- An end probability of at least `c` after every prefix makes survival decay geometrically. -/
theorem survival_le_pow {c : ℝ≥0∞} (hc : ∀ x : List α, c ≤ M.next x {none}) (n : ℕ) :
    M.survival n ≤ (1 - c) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstop := M.mul_survival_le_stopProb (n := n) fun x _ ↦ hc x
    rw [pow_succ, ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (M.survival_ne_top n)
      (M.stopProb_le_survival n)) (M.survival_succ_add_stopProb n)]
    calc M.survival n - M.stopProb n ≤ M.survival n - c * M.survival n := tsub_le_tsub_left hstop _
      _ = M.survival n * (1 - c) := by
        rw [ENNReal.mul_sub fun _ _ ↦ M.survival_ne_top n, mul_one, mul_comm]
      _ ≤ (1 - c) ^ n * (1 - c) := by gcongr

/-! ### Expected length -/

/-- The strings of length at least `m` have total probability at most survival to `m`. -/
theorem tsum_stopProb_add_le (m : ℕ) : ∑' k, M.stopProb (k + m) ≤ M.survival m := by
  refine ENNReal.tsum_le_of_sum_range_le fun N ↦ ?_
  have (N : ℕ) : ∑ k ∈ range N, M.stopProb (k + m) + M.survival (N + m) = M.survival m := by
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ, add_assoc, add_comm (M.stopProb _), Nat.succ_add,
        survival_succ_add_stopProb, ih]
  exact (this N).le.trans' le_self_add

/-- The expected length of the generated string is at most the total survival after the first
step. -/
theorem tsum_length_mul_stringProb_le :
    ∑' x, (x.length : ℝ≥0∞) * M.stringProb x ≤ ∑' n, M.survival (n + 1) := by
  have hlen : ∑' x, (x.length : ℝ≥0∞) * M.stringProb x =
      ∑' n : ℕ, (n : ℝ≥0∞) * M.stopProb n := by
    rw [← (Equiv.sigmaFiberEquiv List.length).tsum_eq, ENNReal.tsum_sigma']
    refine tsum_congr fun n ↦ ?_
    rw [stopProb, ← ENNReal.tsum_mul_left]
    exact tsum_congr fun x ↦ by simp [Equiv.sigmaFiberEquiv, x.2]
  have hcount (n : ℕ) : (n : ℝ≥0∞) * M.stopProb n =
      ∑' j, if j < n then M.stopProb n else 0 := by
    rw [tsum_eq_sum (s := range n) fun j hj ↦ by simp_all, sum_ite_of_true fun j hj ↦
      mem_range.1 hj, sum_const, card_range, nsmul_eq_mul]
  rw [hlen, tsum_congr hcount, ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun j ↦ ?_
  rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := j + 1),
    sum_eq_zero fun k hk ↦ by rw [mem_range] at hk; simp [show ¬ j < k by omega], zero_add]
  have hpos (k : ℕ) : j < k + (j + 1) := by omega
  simp only [hpos, ite_true]
  exact M.tsum_stopProb_add_le (j + 1)

end AutoregressiveSequenceModel
