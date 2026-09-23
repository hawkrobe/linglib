module

public import Linglib.Semantics.Quantification.Numerals.Roundness
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Woodin, Winter, Littlemore, Perlman & Grieve (2024): Large-Scale Patterns of Number Use

This file formalizes the model of number frequency in [woodin-etal-2024]'s corpus study of the
British National Corpus: the log frequency of a number is a linear function of its log
magnitude and of which roundness properties it has (`Model.predicted`). The six properties
are being a multiple of five, being a multiple of ten, and the 10-ness, 2-ness, 2½-ness and
5-ness of [jansen-pollmann-2001], taken with a positive power of ten so that every round
number is a multiple of five (`Property.Holds`). The properties nest: 10-ness, 2-ness and
5-ness entail being a multiple of ten, and every property entails being a multiple of five
(`multipleOf5_mem_of_mem`),
and the unweighted count of properties is the roundness score of the substrate
(`card_properties`). With non-negative weights the roundness term is monotone in the property
set, and a rounder number of comparable magnitude is predicted more frequent exactly when the
weights of its extra properties outweigh the magnitude penalty (`predicted_le_iff`), the case
the study illustrates with 99 and 100 (`predicted_99_le_100_iff`).

## Implementation notes

The fitted coefficients, the ordering of the properties by effect size, the residual analysis
of culturally salient numbers, and the register comparisons are results of the corpus study
and are not restated here; the theorems are over an arbitrary model, with the sign conditions
the study reports as hypotheses.

## References

* [woodin-etal-2024]
* [jansen-pollmann-2001]
* [sigurd-1988]
-/

@[expose] public section

namespace WoodinEtAl2024

open Numerals.Roundness Finset

/-! ### The roundness properties -/

/-- The six roundness properties of the model. -/
inductive Property where
  | multipleOf5
  | multipleOf10
  | tenness
  | twoness
  | twoAndAHalfness
  | fiveness
  deriving DecidableEq, Repr, Fintype

/-- Whether a number has a property; the k-ness properties take a positive power of ten. -/
def Property.Holds : Property → ℕ → Prop
  | .multipleOf5, n => 5 ∣ n
  | .multipleOf10, n => 10 ∣ n
  | .tenness, n => HasKness 10 n
  | .twoness, n => HasKness 20 n
  | .twoAndAHalfness, n => HasKness 25 n
  | .fiveness, n => HasKness 50 n

instance (p : Property) (n : ℕ) : Decidable (p.Holds n) := by
  cases p <;> unfold Property.Holds <;> infer_instance

/-- The properties a number has. -/
def properties (n : ℕ) : Finset Property := univ.filter (·.Holds n)

theorem mem_properties {p : Property} {n : ℕ} : p ∈ properties n ↔ p.Holds n := by
  simp [properties]

/-- 10-ness, 2-ness and 5-ness make a number a multiple of ten. -/
theorem dvd_ten_of_holds {p : Property} {n : ℕ}
    (hp : p = .tenness ∨ p = .twoness ∨ p = .fiveness) (h : p.Holds n) : 10 ∣ n := by
  rcases hp with rfl | rfl | rfl
  · exact h.dvd
  · exact Nat.dvd_trans (by norm_num) h.dvd
  · exact Nat.dvd_trans (by norm_num) h.dvd

/-- Every roundness property makes a number a multiple of five: a number with any property
is a multiple of five. -/
theorem multipleOf5_mem_of_mem {p : Property} {n : ℕ} (h : p ∈ properties n) :
    Property.multipleOf5 ∈ properties n := by
  rw [mem_properties] at h ⊢
  cases p with
  | multipleOf5 => exact h
  | multipleOf10 => exact Nat.dvd_trans (by norm_num) h
  | twoAndAHalfness => exact Nat.dvd_trans (by norm_num) h.dvd
  | tenness => exact Nat.dvd_trans (by norm_num) (dvd_ten_of_holds (.inl rfl) h)
  | twoness => exact Nat.dvd_trans (by norm_num) (dvd_ten_of_holds (.inr (.inl rfl)) h)
  | fiveness => exact Nat.dvd_trans (by norm_num) (dvd_ten_of_holds (.inr (.inr rfl)) h)

/-- The number of properties is the substrate's roundness score. -/
theorem card_properties (n : ℕ) : (properties n).card = roundnessScore n := by
  have hu : (univ : Finset Property) = {.multipleOf5, .multipleOf10, .tenness, .twoness,
      .twoAndAHalfness, .fiveness} := by decide
  rw [properties, card_filter, hu]
  simp only [sum_insert, mem_insert, mem_singleton, reduceCtorEq, or_self, not_false_eq_true,
    sum_singleton, Property.Holds, roundnessScore]
  ring

/-! ### The frequency model -/

/-- A model of log frequency: a coefficient on log magnitude and a weight per roundness
property. -/
structure Model where
  magnitude : ℝ
  weight : Property → ℝ

namespace Model

variable (M : Model)

/-- The predicted log frequency of a number. -/
noncomputable def predicted (n : ℕ) : ℝ :=
  M.magnitude * Real.logb 10 n + ∑ p ∈ properties n, M.weight p

/-- With non-negative weights, the roundness term is monotone in the property set. -/
theorem sum_weight_le_of_subset (hw : ∀ p, 0 ≤ M.weight p) {n m : ℕ}
    (h : properties n ⊆ properties m) :
    ∑ p ∈ properties n, M.weight p ≤ ∑ p ∈ properties m, M.weight p :=
  sum_le_sum_of_subset_of_nonneg h λ p _ _ => hw p

/-- At equal roundness, a negative magnitude coefficient predicts the smaller number more
frequent. -/
theorem predicted_anti (hM : M.magnitude ≤ 0) {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (h : properties n = properties m) : M.predicted m ≤ M.predicted n := by
  unfold predicted
  rw [h]
  have := mul_le_mul_of_nonpos_left
    (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 10) (Nat.cast_pos.mpr hn)
      (Nat.cast_le.mpr hnm)) hM
  linarith

/-- A rounder number is predicted at least as frequent as a less round one exactly when the
weights of its extra properties make up the magnitude difference. -/
theorem predicted_le_iff {n m : ℕ} (h : properties n ⊆ properties m) :
    M.predicted n ≤ M.predicted m ↔
      -M.magnitude * (Real.logb 10 m - Real.logb 10 n) ≤
        ∑ p ∈ properties m \ properties n, M.weight p := by
  unfold predicted
  rw [← sum_sdiff h]
  constructor <;> intro h' <;> linarith

/-- The study's illustration: 100 has every property and 99 none, so 100 is predicted more
frequent exactly when the summed weights make up the magnitude penalty of one part in a
hundred. -/
theorem predicted_99_le_100_iff :
    M.predicted 99 ≤ M.predicted 100 ↔
      -M.magnitude * Real.logb 10 (100 / 99) ≤ ∑ p, M.weight p := by
  have h99 : properties 99 = ∅ := by decide
  have h100 : properties 100 = univ := by decide
  rw [predicted_le_iff M (by rw [h99]; exact empty_subset _), h99, h100, sdiff_empty,
    Real.logb_div (by norm_num) (by norm_num)]
  push_cast
  exact Iff.rfl

end Model

end WoodinEtAl2024
