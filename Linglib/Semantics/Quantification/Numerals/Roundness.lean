module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.DeriveFintype

/-!
# Numeral roundness

A number has `k`-ness when it is a digit times `k` times a power of ten, Jansen and Pollmann's
`k × (1–9 × 10ⁿ)`. Sigurd, Jansen and Pollmann, and Woodin et al. take a number's roundness to be
carried by six properties: being a multiple of five or of ten, and 10-ness, 2-ness, 2½-ness and
5-ness. Following Woodin et al. the `k`-ness properties require a positive power of ten, which is
`10 k`-ness, so every round number is a multiple of five. The roundness score of a number is the
number of these properties it has.

## Main definitions

* `Numerals.Roundness.HasKness`: `k`-ness, decidable.
* `Numerals.Roundness.Property`: the six roundness properties.
* `Numerals.Roundness.roundnessScore`: the number of roundness properties a number has.

## Implementation notes

Woodin et al.'s regression weights the properties unequally as predictors of frequency, 10-ness
strongest (β = 4.46), then 2½-ness (3.84), 5-ness (3.39), 2-ness (2.74), multiple of ten (2.45)
and multiple of five (0.06); the score counts them equally. Jansen and Pollmann's own definition
allows the zeroth power, see `Studies/JansenPollmann2001.lean`.

## References

* [sigurd-1988]
* [jansen-pollmann-2001]
* [woodin-etal-2024]
-/

@[expose] public section

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

/-! ### The roundness properties -/

/-- The six roundness properties of a number. -/
inductive Property where
  | multipleOf5
  | multipleOf10
  | tenness
  | twoness
  | twoAndAHalfness
  | fiveness
  deriving DecidableEq, Repr, Fintype

/-- A number has a roundness property; the `k`-ness properties take a positive power of ten, so
2-, 2½-, 5- and 10-ness are 20-, 25-, 50- and 10-ness. -/
def Property.Holds : Property → ℕ → Prop
  | .multipleOf5, n => 5 ∣ n
  | .multipleOf10, n => 10 ∣ n
  | .tenness, n => HasKness 10 n
  | .twoness, n => HasKness 20 n
  | .twoAndAHalfness, n => HasKness 25 n
  | .fiveness, n => HasKness 50 n

instance (p : Property) (n : ℕ) : Decidable (p.Holds n) := by
  cases p <;> unfold Property.Holds <;> infer_instance

/-- The roundness properties a number has. -/
def properties (n : ℕ) : Finset Property := Finset.univ.filter (·.Holds n)

@[simp] theorem mem_properties {p : Property} {n : ℕ} : p ∈ properties n ↔ p.Holds n := by
  simp [properties]

/-! ### The roundness score -/

/-- The roundness score of a number is the number of roundness properties it has. -/
def roundnessScore (n : ℕ) : ℕ := (properties n).card

/-- The roundness score counts the six properties one by one. -/
theorem roundnessScore_eq (n : ℕ) : roundnessScore n =
    (if 5 ∣ n then 1 else 0) + (if 10 ∣ n then 1 else 0) + (if HasKness 10 n then 1 else 0) +
      (if HasKness 20 n then 1 else 0) + (if HasKness 25 n then 1 else 0) +
        (if HasKness 50 n then 1 else 0) := by
  have hu : (Finset.univ : Finset Property) = {.multipleOf5, .multipleOf10, .tenness, .twoness,
      .twoAndAHalfness, .fiveness} := by decide
  rw [roundnessScore, properties, Finset.card_filter, hu]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self,
    not_false_eq_true, Finset.sum_singleton, Property.Holds]
  ring

theorem roundnessScore_le_six (n : ℕ) : roundnessScore n ≤ 6 :=
  (Finset.card_le_univ _).trans_eq rfl

example : roundnessScore 100 = 6 := by decide
example : roundnessScore 50 = 5 := by decide
example : roundnessScore 20 = 4 := by decide
example : roundnessScore 110 = 2 := by decide
example : roundnessScore 7 = 0 := by decide

end Numerals.Roundness
