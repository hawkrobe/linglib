import Mathlib.Data.Nat.Log

/-!
# Graded Numeral Roundness (k-ness Model)

Framework-agnostic infrastructure for graded numeral roundness,
following [sigurd-1988], [jansen-pollmann-2001], and [woodin-etal-2023].

A number n has **k-ness** if it lies in [jansen-pollmann-2001]'s set
k × (1–9 × 10ⁿ): n = m × k × 10^b with 1 ≤ m ≤ 9 — so 10-ness is the
k = 1 family, per their own example "70 has only 10-ness". The roundness
score follows [woodin-etal-2023] in requiring b ≥ 1, which drops the
single digits from 10-ness and 15, 45, … from 5-ness; since k-ness with
b ≥ 1 is 10k-ness, one predicate serves both (cf.
`Studies/JansenPollmann2001.lean` for the divergence).

The 6 properties, ordered by strength as frequency predictors in
[woodin-etal-2023]'s negative binomial regression (strongest first):
10-ness (β = 4.46), 2.5-ness (β = 3.84), 5-ness (β = 3.39),
2-ness (β = 2.74), multiple of 10 (β = 2.45), multiple of 5 (β = 0.06);
the 2-ness and multiple-of-10 credible intervals overlap.

## Main definitions

- `HasKness`: the k-ness properties as one decidable predicate;
  `hasKness_ten_mul_iff` is the positive-exponent reading
- `roundnessScore`: count of the six properties that hold (0–6)
- `RoundnessGrade`, `roundnessGrade`: the score binned into 4 levels
- `contextualRoundnessScore`, `roundnessInContext`: k-ness relative to a
  non-standard base (dozens, minutes)

## References

* [C. J. M. Jansen, M. M. W. Pollmann, *On round numbers: pragmatic aspects of numerical
  expressions* (2001)][jansen-pollmann-2001]
* [B. Sigurd, *Round numbers* (1988)][sigurd-1988]
* [G. Woodin, B. Winter, J. Littlemore, M. Perlman, J. Grieve, *Large-scale patterns of
  number use in spoken and written English* (2023)][woodin-etal-2023]
* [M. Krifka, *Approximate interpretation of number words* (2007)][krifka-2007]
* [C. Cummins, *Constraints on numerical expressions* (2015)][cummins-2015]
-/

namespace Numerals.Roundness

/-! ### k-ness -/

/-- `n` has `k`-ness: `n = m × k × 10^b` for some digit `1 ≤ m ≤ 9` and exponent `b`, that
is `n ∈ k × {1, …, 9} × 10^ℕ` ([jansen-pollmann-2001]). Their 10-ness is `HasKness 1`
(70 has only 10-ness), 2½-ness of `n` is 5-ness of `2n`, and restricting the exponent to
`b ≥ 1` is `k`-ness with `k` scaled by ten. -/
def HasKness (k n : ℕ) : Prop := ∃ b m, 1 ≤ m ∧ m ≤ 9 ∧ n = m * k * 10 ^ b

/-- The exponent of a `k`-ness witness is at most `log₁₀ n`, so `k`-ness is decidable. -/
theorem hasKness_iff_exists_le_log {k n : ℕ} :
    HasKness k n ↔ ∃ b ≤ Nat.log 10 n, ∃ m < 10, 1 ≤ m ∧ n = m * k * 10 ^ b := by
  constructor
  · rintro ⟨b, m, hm, hm9, rfl⟩
    obtain rfl | hk := Nat.eq_zero_or_pos k
    · exact ⟨0, Nat.zero_le _, m, by omega, hm, by simp⟩
    refine ⟨b, Nat.le_log_of_pow_le (by decide) ?_, m, by omega, hm, rfl⟩
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hm hk)
  · rintro ⟨b, -, m, hm, hm1, rfl⟩
    exact ⟨b, m, hm1, by omega, rfl⟩

instance (k n : ℕ) : Decidable (HasKness k n) :=
  decidable_of_iff _ hasKness_iff_exists_le_log.symm

/-- `k`-ness forces divisibility by `k`. -/
theorem HasKness.dvd {k n : ℕ} (h : HasKness k n) : k ∣ n := by
  obtain ⟨b, m, -, -, rfl⟩ := h
  exact Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_left k m) _

/-- `10k`-ness is `k`-ness with a positive exponent. -/
theorem hasKness_ten_mul_iff {k n : ℕ} :
    HasKness (10 * k) n ↔ ∃ b m, 1 ≤ m ∧ m ≤ 9 ∧ n = m * k * 10 ^ (b + 1) := by
  simp only [HasKness, Nat.pow_succ]
  constructor <;> rintro ⟨b, m, h1, h9, rfl⟩ <;> exact ⟨b, m, h1, h9, by ac_rfl⟩

/-! ### Roundness score

The six graded roundness properties of [sigurd-1988] and
[jansen-pollmann-2001] — multiple of 5, multiple of 10, 2-ness, 2.5-ness,
5-ness, 10-ness — counted equally. The count predicts numeral frequency
and pragmatic behavior ([woodin-etal-2023]). -/

/-- Count of true roundness properties (0–6). Higher = rounder. The k-ness properties
are taken with a positive exponent, following [woodin-etal-2023], so 2-, 2½-, 5- and
10-ness are `HasKness 20`, `HasKness 25`, `HasKness 50` and `HasKness 10`. -/
def roundnessScore (n : ℕ) : ℕ :=
  (if 5 ∣ n then 1 else 0) + (if 10 ∣ n then 1 else 0) +
  (if HasKness 20 n then 1 else 0) + (if HasKness 25 n then 1 else 0) +
  (if HasKness 50 n then 1 else 0) + (if HasKness 10 n then 1 else 0)

/-- Maximum possible roundness score. -/
def maxRoundnessScore : ℕ := 6

/-! ### Roundness grade (binned score) -/

/--
Binned roundness grade for use in width/tolerance functions.

Collapses the 0–6 score into 4 levels to avoid duplicating
step-function logic across Theory files.
-/
inductive RoundnessGrade where
  /-- score ≥ 5 (e.g., 100, 50, 200) -/
  | high
  /-- score 3–4 (e.g., 20, 40) -/
  | moderate
  /-- score 1–2 (e.g., 110, 15) -/
  | low
  /-- score 0 (e.g., 7, 99) -/
  | none
  deriving Repr, DecidableEq

/-- Classify a number into a roundness grade. -/
def roundnessGrade (n : ℕ) : RoundnessGrade :=
  if roundnessScore n ≥ 5 then .high
  else if roundnessScore n ≥ 3 then .moderate
  else if roundnessScore n ≥ 1 then .low
  else .none

/-! ### Context-sensitive roundness -/

/--
Count k-ness-like properties relative to a non-standard base.

For base b, checks divisibility by b, 2b, 5b, and 10b — mirroring
the standard k-ness properties but on a different scale.

Examples:
- contextualRoundnessScore 48 12 = 2 (48 ÷ 12 = 4, 48 ÷ 24 = 2)
- contextualRoundnessScore 120 12 = 4 (divides by 12, 24, 60, 120)
-/
def contextualRoundnessScore (n : ℕ) (base : ℕ) : ℕ :=
  if base ≤ 1 ∨ n = 0 then 0
  else
    (if base ∣ n then 1 else 0) + (if base * 2 ∣ n then 1 else 0) +
    (if base * 5 ∣ n then 1 else 0) + (if base * 10 ∣ n then 1 else 0)

/--
Context-sensitive roundness: compose default k-ness with a non-standard base.

On a base-12 (dozens) scale, 48 = 4 × 12 is "round" even though its
default k-ness score is 0. On base-60 (minutes), 120 = 2 × 60 is round.

The contextual score derives from actual divisibility properties relative
to the base (not a flat bonus), paralleling how standard k-ness derives
from divisibility by 2/2.5/5/10 × powers of 10.
-/
def roundnessInContext (n : ℕ) (base : ℕ) : ℕ :=
  max (roundnessScore n) (contextualRoundnessScore n base)

/-! ### Per-datum verification -/

example : roundnessScore 100 = 6 := by decide
example : roundnessScore 50 = 5 := by decide
example : roundnessScore 7 = 0 := by decide
example : roundnessScore 1000 = 6 := by decide
example : roundnessScore 200 = 6 := by decide
example : roundnessScore 110 = 2 := by decide
example : roundnessScore 20 = 4 := by decide

example : roundnessGrade 100 = .high := by decide
example : roundnessGrade 50 = .high := by decide
example : roundnessGrade 110 = .low := by decide
example : roundnessGrade 7 = .none := by decide

example : contextualRoundnessScore 48 12 = 2 := by decide
example : contextualRoundnessScore 120 12 = 4 := by decide
-- contextual score beats default; nothing on base-10; default beats contextual
example : roundnessInContext 48 12 = 2 := by decide
example : roundnessInContext 48 10 = 0 := by decide
example : roundnessInContext 100 10 = 6 := by decide

/-- The roundness score never exceeds `maxRoundnessScore`: each of the six
properties contributes at most 1. -/
theorem roundnessScore_le_max (n : ℕ) : roundnessScore n ≤ maxRoundnessScore := by
  unfold roundnessScore maxRoundnessScore
  split_ifs <;> omega

/-- Multiples of 10 have roundness score ≥ 2 (multiple-of-5 and
multiple-of-10 both hold). The keystone for downstream sorry-free proofs. -/
theorem score_ge_two_of_div10 (n : ℕ) (h10 : 10 ∣ n) :
    2 ≤ roundnessScore n := by
  have h5 : 5 ∣ n := Nat.dvd_trans ⟨2, rfl⟩ h10
  rw [roundnessScore, if_pos h5, if_pos h10]
  omega

end Numerals.Roundness
