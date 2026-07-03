/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Quantification.Numerals.Roundness
import Linglib.Syntax.Numeral.Composition
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.GCD

/-!
# [jansen-pollmann-2001]: On Round Numbers
[jansen-pollmann-2001] [sigurd-1988] [krifka-2007] [woodin-etal-2023]

[jansen-pollmann-2001] operationalize roundness as *relative* suitability
for approximation contexts (frequency after Dutch *ongeveer* 'about') and
find it carried by four numerical properties — 10-ness, 2-ness, 5-ness,
and (following [sigurd-1988]) 2½-ness: membership in `[k × (1–9 × 10ⁿ)]`
(their p. 198). Their explanation (pp. 200–201) is the **principle of
favourite quantities**: doubling and halving (sometimes followed by
halving again) are the basic means of manipulating quantities, so the
round-number unit inventory is the orbit of the decimal base powers under
these operations — exactly the four k-families (`favUnit_iff`), and
provably not the 3-family (`not_favUnit_three_mul_pow`; their p. 199:
3-, 4-, 6-, 7-ness contribute nothing).

Two-number approximative expressions (*about 5 or 6 books*) obey the
**revised sequence rule** (their p. 197): the pair consists of consecutive
members of an arithmetic sequence whose ratio and first member are
`1×10ⁿ`, `2×10ⁿ`, or `½×10ⁿ`. Quarters, which do round single numbers
(2½-ness), are absent from pairs (`quarter_unit_not_seqRatio`).

Their p. 198 definition allows the zeroth power (`hasKnessOrig`);
`Roundness.HasKness` follows [woodin-etal-2023]'s b ≥ 1 restriction
(their fn. 3). The divergence matters downstream: under the original,
15 has 5-ness (`fifteen_has_orig_fiveness`) — roundness that the
restricted variant, and hence `Precision.inferPrecisionMode`, misses at
15, 45, …. Reading this paper also corrected `Roundness`'s 10-ness: it is
the k = 1 family (divisors 10, 100, …) — their own example "70 has only
10-ness" — not the k = 10 family.

Their regression (frequency from magnitude n⁻¹, n⁻² plus the four
properties, R² = 0.968, p. 200) stays prose per the no-regression-theorems
rule, as does the FA operationalization itself.

## Main definitions

- `QuantityOp`, `IsFavUnit`: doubling/halving over decimal base powers
- `SeqRatio`, `SeqPair`: the revised sequence rule
- `hasKnessOrig`: their original (b ≥ 0) k-ness

## Main results

- `favUnit_iff`: the favourite units are exactly the four k-families
- `not_favUnit_three_mul_pow`: the 3-family is not derivable — why the
  inventory stops at four properties
- `quarter_unit_not_seqRatio`: quarters round single numbers, not pairs
- their p. 198 examples and p. 196 pair judgments, checked by `decide`
- `fifteen_has_orig_fiveness`: the b ≥ 0 vs b ≥ 1 divergence at 15
-/

namespace JansenPollmann2001

open Semantics.Numerals.Roundness

/-! ### The principle of favourite quantities (their pp. 200–201) -/

/-- The basic quantity-manipulation operations: "doubling and halving
(sometimes followed by halving again)". -/
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

/-- A favourite unit: a decimal base power manipulated by one quantity
operation. -/
def IsFavUnit (q : ℚ) : Prop :=
  ∃ (op : QuantityOp) (n : ℕ), q = op.apply (10 ^ n)

/-- The favourite units are exactly the four k-ness families: powers of
ten, their doubles, their halves, and their quarters. -/
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

/-- No quantity operation reaches the 3-family: the structural reason the
roundness inventory has exactly four properties (their p. 199: 3-, 4-, 6-,
7-ness contribute nothing to frequency). -/
theorem not_favUnit_three_mul_pow (m : ℕ) : ¬ IsFavUnit (3 * 10 ^ m) := by
  have h3 : ∀ j : ℕ, ¬ (3 ∣ 10 ^ j) := fun j hd => by
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

/-! ### The revised sequence rule (their pp. 196–197)

Two-number approximative expressions ([about 5 or 6 books]) consist of
consecutive members of an arithmetic sequence whose ratio equals its first
member and is `1×10ⁿ`, `2×10ⁿ`, or `½×10ⁿ` (in ℕ, the half-family is
`5×10ⁿ`). The original rule also allowed `¼×10ⁿ`; the revision drops it
(quarter-ratio pairs are under 0.5% in all four corpora). -/

/-- A ratio licensed by the revised sequence rule. -/
def SeqRatio (r : ℕ) : Prop :=
  ∃ n < 11, r = 10 ^ n ∨ r = 2 * 10 ^ n ∨ r = 5 * 10 ^ n

instance (r : ℕ) : Decidable (SeqRatio r) :=
  inferInstanceAs (Decidable (∃ n < 11, _ ∨ _ ∨ _))

/-- The revised sequence rule: `[a, b]` are consecutive members of the
sequence `r, 2r, 3r, …` for a licensed ratio `r`. -/
def SeqPair (a b : ℕ) : Prop :=
  ∃ r ≤ a, 0 < r ∧ SeqRatio r ∧ r ∣ a ∧ b = a + r

instance (a b : ℕ) : Decidable (SeqPair a b) :=
  inferInstanceAs (Decidable (∃ r ≤ a, _ ∧ _ ∧ _ ∧ _))

-- Their p. 196 pairs: attested combinations conform to the rule,
-- their starred non-combinations do not, and the revision excludes
-- quarter-ratio pairs (their p. 197).
example : SeqPair 3 4 := by decide      -- sequence 1, 2, 3, 4
example : SeqPair 40 50 := by decide    -- sequence 10, 20, …, 50
example : SeqPair 18 20 := by decide    -- sequence 2, 4, …, 20
set_option maxRecDepth 2048 in
example : SeqPair 100 150 := by decide  -- sequence 50, 100, 150
example : ¬ SeqPair 1 3 := by decide    -- [*about 1 or 3]
example : ¬ SeqPair 5 7 := by decide    -- [*about 5 or 7]
example : ¬ SeqPair 6 9 := by decide    -- [*about 6 or 9]
example : ¬ SeqPair 40 80 := by decide  -- [*about 40 or 80]
set_option maxRecDepth 2048 in
example : ¬ SeqPair 100 125 := by decide -- ratio ¼ × 10²: excluded

/-- Quarters split single-number roundness from pair formation: `25` is a
favourite unit (twice-halved `10²`, whence 2½-ness) but not a licensed
sequence ratio — their pp. 197, 199–200 asymmetry. -/
theorem quarter_unit_not_seqRatio : IsFavUnit 25 ∧ ¬ SeqRatio 25 :=
  ⟨⟨.halfAgain, 2, by norm_num [QuantityOp.apply]⟩, by decide⟩

/-! ### The original k-ness and the b ≥ 1 restriction (their p. 198) -/

/-- Their original k-ness: `n ∈ [k × (1–9 × 10ᵇ)]` with `b ≥ 0` — 10-ness
is `k = 1`. `Roundness.HasKness` is this with [woodin-etal-2023]'s
`b ≥ 1` restriction. Search bounded as there. -/
def hasKnessOrig (n k : ℕ) : Prop :=
  ∃ b < 11, ∃ m < 10, 1 ≤ m ∧ n = m * k * 10 ^ b

instance (n k : ℕ) : Decidable (hasKnessOrig n k) :=
  inferInstanceAs (Decidable (∃ b < 11, ∃ m < 10, _ ∧ _))

/-- The restricted variant entails the original. -/
theorem hasKnessOrig_of_hasKness {n k : ℕ} (h : HasKness n k) :
    hasKnessOrig n k :=
  let ⟨b, hb, _, hm⟩ := h
  ⟨b, hb, hm⟩

-- Their p. 198 examples, under the original definition: "40 has 10-ness,
-- 2-ness, and 5-ness; 8 has 10-ness and 2-ness but no 5-ness; 300 has
-- 10-ness and 5-ness but no 2-ness; 70 has only 10-ness; 61 has none."
example : hasKnessOrig 40 1 ∧ hasKnessOrig 40 2 ∧ hasKnessOrig 40 5 := by
  decide
example : hasKnessOrig 8 1 ∧ hasKnessOrig 8 2 ∧ ¬ hasKnessOrig 8 5 := by
  decide
example : hasKnessOrig 300 1 ∧ hasKnessOrig 300 5 ∧ ¬ hasKnessOrig 300 2 := by
  decide
example : hasKnessOrig 70 1 ∧ ¬ hasKnessOrig 70 2 ∧ ¬ hasKnessOrig 70 5 := by
  decide
example : ¬ hasKnessOrig 61 1 ∧ ¬ hasKnessOrig 61 2 ∧ ¬ hasKnessOrig 61 5 := by
  decide

/-- The divergence that matters downstream: under the original definition
15 has 5-ness (15 = 3 × 5 × 10⁰), which the b ≥ 1 variant drops — the
source of the 15/45-idealization noted at
`Precision.inferPrecisionMode`. -/
theorem fifteen_has_orig_fiveness : hasKnessOrig 15 5 ∧ ¬ HasKness 15 5 := by
  decide

/-! ### 10-ness as expression shape ([hurford-1975]) -/

/-- 10-ness is two-word expressibility: `n` has 10-ness iff it is the
value of a digit×base PHRASE — [hurford-1975]'s `[NUMBER M]` with a digit
NUMBER and a pure ten-power M (*forty*, *four hundred*, …). The
favourite-quantity properties are facts about numeral expression shape. -/
theorem hasKness_one_iff_phrase (n : ℕ) :
    HasKness n 1 ↔ ∃ m ≤ 8, ∃ k ≤ 9,
      n = (Syntax.Numeral.Phrase.mk (.tally m) (.tenPow k)).value := by
  simp only [Syntax.Numeral.Phrase.value_tally_tenPow]
  constructor
  · rintro ⟨b, hb, hb1, m, hm, hm1, rfl⟩
    exact ⟨m - 1, by omega, b - 1, by omega, by
      rw [Nat.sub_add_cancel hm1, Nat.sub_add_cancel hb1, mul_one]⟩
  · rintro ⟨m, hm, k, hk, rfl⟩
    exact ⟨k + 1, by omega, by omega, m + 1, by omega, by omega, by
      rw [mul_one]⟩

end JansenPollmann2001
