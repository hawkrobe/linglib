/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.Examples.JansenPollmann2001
import Linglib.Semantics.Quantification.Numerals.Roundness
import Linglib.Syntax.Category.Numeral.Composition
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.GCD

/-!
# Jansen and Pollmann (2001): On round numbers

This file formalizes [jansen-pollmann-2001]'s account of what makes a number round. Roundness
is operationalized as relative suitability for approximation contexts, the frequency of a
number after Dutch *ongeveer* 'about', and is carried by four numerical properties: 10-ness,
2-ness, 5-ness, and, following [sigurd-1988], 2½-ness, membership in the set
`k × (1–9 × 10ⁿ)` for the respective `k` (p. 198), the substrate's `Roundness.HasKness`. The
paper's explanation is the principle of favourite quantities (pp. 200–201): doubling and
halving, sometimes followed by halving again, are the basic means of manipulating quantities,
so the round units are the orbit of the decimal base powers under these operations, which
`favUnit_iff` identifies with the four families and `not_favUnit_three_mul_pow` separates from
the 3-family, whose contribution to frequency the paper finds to be nil (p. 199).

Two-number approximative expressions, *about 5 or 6 books*, obey the revised sequence rule
(pp. 196–197): the pair consists of consecutive members of an arithmetic sequence whose ratio
and first member are `1 × 10ⁿ`, `2 × 10ⁿ`, or `½ × 10ⁿ`; `seqPair_iff` reduces the rule to a
condition on the pair's difference, and `pair_rows` checks it against the paper's attested and
starred pairs, including the quarter pair the revision drops. Quarters, which round single
numbers, are thus absent from pairs (`quarter_unit_not_seqRatio`). The paper's regression of
frequency on magnitude and the four properties stays in prose.

## Implementation notes

* The paper's definition allows the zeroth power; `Roundness.roundnessScore` follows
  [woodin-etal-2024] in requiring the first, which is `k`-ness with `k` scaled by ten. The
  divergence shows at 15, which has 5-ness under the paper's definition but not 50-ness
  (`fifteen_hasKness_five_not_fifty`), so `Precision.inferPrecisionMode` misses it. The paper's
  10-ness is the `k = 1` family, as its example *70 has only 10-ness* shows.

## References

* [jansen-pollmann-2001]
* [sigurd-1988]
* [woodin-etal-2024]
* [hurford-1975]
-/

namespace JansenPollmann2001

open Data.Examples Numerals.Roundness

/-! ### The principle of favourite quantities (pp. 200–201) -/

/-- The basic quantity-manipulation operations: doubling and halving, sometimes followed by
halving again. -/
inductive QuantityOp where
  /-- Leave the base quantity as is. -/
  | id
  /-- Double it. -/
  | double
  /-- Halve it. -/
  | half
  /-- Halve it twice. -/
  | halfAgain
  deriving DecidableEq, Repr

/-- Apply a quantity operation. -/
def QuantityOp.apply : QuantityOp → ℚ → ℚ
  | .id, q => q
  | .double, q => 2 * q
  | .half, q => q / 2
  | .halfAgain, q => q / 4

/-- A favourite unit: a decimal base power manipulated by one quantity operation. -/
def IsFavUnit (q : ℚ) : Prop :=
  ∃ (op : QuantityOp) (n : ℕ), q = op.apply (10 ^ n)

/-- The favourite units are exactly the four `k`-ness families: powers of ten, their doubles,
their halves, and their quarters. -/
theorem favUnit_iff (q : ℚ) :
    IsFavUnit q ↔
      ∃ n : ℕ, q = 10 ^ n ∨ q = 2 * 10 ^ n ∨ q = 10 ^ n / 2 ∨ q = 10 ^ n / 4 := by
  constructor
  · rintro ⟨op, n, rfl⟩
    exact ⟨n, by cases op <;> simp [QuantityOp.apply]⟩
  · rintro ⟨n, h | h | h | h⟩
    exacts [⟨.id, n, h⟩, ⟨.double, n, h⟩, ⟨.half, n, h⟩, ⟨.halfAgain, n, h⟩]

/-- Halving a base power lands on the 5-family. -/
theorem half_pow (n : ℕ) : (10 : ℚ) ^ (n + 1) / 2 = 5 * 10 ^ n := by
  rw [pow_succ]; ring

/-- Halving twice lands on the 2½-family. -/
theorem halfAgain_pow (n : ℕ) : (10 : ℚ) ^ (n + 1) / 4 = 5 / 2 * 10 ^ n := by
  rw [pow_succ]; ring

/-- No quantity operation reaches the 3-family: the structural reason the roundness inventory
has exactly four properties, 3-, 4-, 6-, and 7-ness contributing nothing to frequency
(p. 199). -/
theorem not_favUnit_three_mul_pow (m : ℕ) : ¬ IsFavUnit (3 * 10 ^ m) := by
  have h3 : ∀ j : ℕ, ¬ (3 ∣ 10 ^ j) := λ j hd => by
    have h1 := (Nat.Coprime.pow_right j (show Nat.Coprime 3 10 by norm_num)).eq_one_of_dvd hd
    omega
  rintro ⟨op, n, h⟩
  cases op <;> simp only [QuantityOp.apply] at h
  · exact h3 n ⟨10 ^ m, by exact_mod_cast h.symm⟩
  · have hn : 3 * 10 ^ m = 2 * 10 ^ n := by exact_mod_cast h
    exact h3 n ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num)) ⟨10 ^ m, hn.symm⟩)
  · have h2 : (6 : ℚ) * 10 ^ m = 10 ^ n := by field_simp at h; linarith
    have hn : 6 * 10 ^ m = 10 ^ n := by exact_mod_cast h2
    exact h3 n ⟨2 * 10 ^ m, by omega⟩
  · have h2 : (12 : ℚ) * 10 ^ m = 10 ^ n := by field_simp at h; linarith
    have hn : 12 * 10 ^ m = 10 ^ n := by exact_mod_cast h2
    exact h3 n ⟨4 * 10 ^ m, by omega⟩

/-! ### The revised sequence rule (pp. 196–197)

Two-number approximative expressions consist of consecutive members of an arithmetic sequence
whose ratio equals its first member and is `1 × 10ⁿ`, `2 × 10ⁿ`, or `½ × 10ⁿ`, in `ℕ` the
family `5 × 10ⁿ`. The original rule also allowed `¼ × 10ⁿ`; the revision drops it, quarter-ratio
pairs being under half a percent in all four corpora. -/

/-- A ratio licensed by the revised sequence rule. -/
def SeqRatio (r : ℕ) : Prop :=
  ∃ n < 11, r = 10 ^ n ∨ r = 2 * 10 ^ n ∨ r = 5 * 10 ^ n

instance (r : ℕ) : Decidable (SeqRatio r) :=
  inferInstanceAs (Decidable (∃ n < 11, _ ∨ _ ∨ _))

/-- The revised sequence rule: `[a, b]` are consecutive members of the sequence `r, 2r, 3r, …`
for a licensed ratio `r`. -/
def SeqPair (a b : ℕ) : Prop :=
  ∃ r ≤ a, 0 < r ∧ SeqRatio r ∧ r ∣ a ∧ b = a + r

/-- The ratio of a pair is its difference, so the rule is a condition on `b - a`. -/
theorem seqPair_iff (a b : ℕ) :
    SeqPair a b ↔ a < b ∧ b - a ≤ a ∧ SeqRatio (b - a) ∧ b - a ∣ a := by
  constructor
  · rintro ⟨r, hr, h0, hs, hd, rfl⟩
    refine ⟨by omega, ?_, ?_, ?_⟩ <;> simpa using ‹_›
  · rintro ⟨hab, hle, hs, hd⟩
    exact ⟨b - a, hle, by omega, hs, hd, by omega⟩

instance (a b : ℕ) : Decidable (SeqPair a b) :=
  decidable_of_iff _ (seqPair_iff a b).symm

/-- Quarters split single-number roundness from pair formation: `25` is a favourite unit, twice
halved `10²`, whence 2½-ness, but not a licensed sequence ratio (pp. 197, 199–200). -/
theorem quarter_unit_not_seqRatio : IsFavUnit 25 ∧ ¬ SeqRatio 25 :=
  ⟨⟨.halfAgain, 2, by norm_num [QuantityOp.apply]⟩, by decide⟩

/-! ### The rows -/

/-- A two-number approximative expression of the paper with its acceptability. -/
def pairRow (r : LinguisticExample) : Option (ℕ × ℕ × Bool) := do
  let a ← r.nat? "first"
  let b ← r.nat? "second"
  pure (a, b, decide (r.judgment = .acceptable))

/-- The attested and starred pairs of pp. 196–197. -/
def pairData : List (ℕ × ℕ × Bool) := Examples.all.filterMap pairRow

/-- The attested pairs obey the revised sequence rule and the starred pairs, and the quarter
pair, do not. -/
theorem pair_rows : ∀ d ∈ pairData, d.2.2 = true ↔ SeqPair d.1 d.2.1 := by decide +kernel

/-- A single number with the three properties the paper reads off it: 10-ness, 2-ness, and
5-ness. -/
def numberRow (r : LinguisticExample) : Option (ℕ × Bool × Bool × Bool) := do
  let n ← r.nat? "n"
  let ten ← r.parse? "tenness" [("true", true), ("false", false)]
  let two ← r.parse? "twoness" [("true", true), ("false", false)]
  let five ← r.parse? "fiveness" [("true", true), ("false", false)]
  pure (n, ten, two, five)

/-- The numbers of p. 198. -/
def numberData : List (ℕ × Bool × Bool × Bool) := Examples.all.filterMap numberRow

/-- The paper's readings of 10-ness, 2-ness, and 5-ness, 10-ness being the `k = 1` family. -/
theorem number_rows : ∀ d ∈ numberData,
    (d.2.1 = true ↔ HasKness 1 d.1) ∧ (d.2.2.1 = true ↔ HasKness 2 d.1) ∧
      (d.2.2.2 = true ↔ HasKness 5 d.1) := by
  decide +kernel

/-! ### `k`-ness and the `b ≥ 1` restriction -/

/-- The divergence that matters downstream: under the paper's definition 15 has 5-ness, as
`15 = 3 × 5 × 10⁰`, which the `b ≥ 1` variant, 50-ness, drops. -/
theorem fifteen_hasKness_five_not_fifty : HasKness 5 15 ∧ ¬ HasKness 50 15 := by
  decide

/-! ### 10-ness as expression shape ([hurford-1975]) -/

/-- 10-ness is two-word expressibility: `n` has 10-ness iff it is the value of a digit × base
phrase, [hurford-1975]'s `[NUMBER M]` with a digit NUMBER and a pure ten-power M, *forty*,
*four hundred*. The favourite-quantity properties are facts about numeral expression shape. -/
theorem hasKness_ten_iff_phrase (n : ℕ) :
    HasKness 10 n ↔ ∃ m ≤ 8, ∃ k,
      n = (Syntax.Numeral.Phrase.mk (.tally m) (.tenPow k)).value := by
  simp only [Syntax.Numeral.Phrase.value_tally_tenPow]
  constructor
  · rintro ⟨b, m, hm1, hm, rfl⟩
    exact ⟨m - 1, by omega, b, by rw [Nat.sub_add_cancel hm1, Nat.mul_assoc, ← Nat.pow_succ']⟩
  · rintro ⟨m, hm, k, rfl⟩
    exact ⟨k, m + 1, by omega, by omega, by rw [Nat.mul_assoc, Nat.pow_succ']⟩

end JansenPollmann2001
