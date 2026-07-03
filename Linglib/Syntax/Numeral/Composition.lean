/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring

/-!
# Hurford's universal numeral grammar
[hurford-1975] [ionin-matushansky-2006]

[hurford-1975]'s phrase-structure grammar for number-names (his (2),
p. 19), proposed as the universal base of numeral systems:

- `NUMBER → {one | PHRASE} (NUMBER)`
- `PHRASE → NUMBER M`
- `M → {ten | NUMBER M}`

with the three projection rules of his (23) (pp. 29–30): the value of a
NUMBER is the **sum** of its immediate constituents, of a PHRASE the
**product**, and of an M the second constituent raised to the **power**
of the first. So *twenty-three* is `[[two ten] three]` = 2·10 + 3,
*thousand* is `[three ten]` = 10³.

His deeper claim ((26)–(29)): the three rules are one operation,
`CALCULATE`, indexed by constituent *depth* — NUMBERs (depth 1) add,
PHRASEs (depth 2) multiply, Ms (depth 3) exponentiate, each operation the
iteration of the one before. `value_eq_calculate` states the unification;
`calculate_succ_iterate` states the iteration ladder its complexity
ordering rests on.

Consumers: `Studies/IoninMatushansky2006.lean` (their §3.3 adopts
Hurford's cardinals-as-nouns; their §4.3 order conventions constrain
which of these structures surface) and `Studies/JansenPollmann2001.lean`
(10-ness as digit×M expressibility).

## Main declarations

- `Number`, `Phrase`, `M`: the three syntactic categories, with `value`
- `Number.tally`, `M.tenPow`: canonical digit and base-power structures
- `calculate`: the depth-indexed arithmetic (his (26))

## Main results

- `value_eq_calculate`: the three projection rules are `calculate` at
  depths 1–3
- `calculate_succ_iterate`: each operation iterates the previous one
- `Number.exists_value_eq`: every positive number is expressible
  (the tally structure his rule schema (6) generates)
-/

namespace Syntax.Numeral

/-! ### The phrase-structure categories (his (2)) -/

mutual
/-- `NUMBER → {one | PHRASE} (NUMBER)`. -/
inductive Number where
  /-- `NUMBER → one`. -/
  | one : Number
  /-- `NUMBER → one NUMBER`. -/
  | oneAnd (rest : Number) : Number
  /-- `NUMBER → PHRASE`. -/
  | phrase (p : Phrase) : Number
  /-- `NUMBER → PHRASE NUMBER` — e.g. *twenty-three*. -/
  | phraseAnd (p : Phrase) (rest : Number) : Number
  deriving Repr

/-- `PHRASE → NUMBER M` — e.g. *two hundred*. -/
inductive Phrase where
  | mk (n : Number) (m : M) : Phrase
  deriving Repr

/-- `M → {ten | NUMBER M}` — the base-word hierarchy: *ten*, *hundred*
(`[two ten]` = 10²), *thousand* (`[three ten]` = 10³), …. -/
inductive M where
  | ten : M
  | mk (n : Number) (m : M) : M
  deriving Repr
end

/-! ### The projection rules (his (23)) -/

mutual
/-- The value of a NUMBER: the sum of its immediate constituents. -/
def Number.value : Number → ℕ
  | .one => 1
  | .oneAnd rest => 1 + rest.value
  | .phrase p => p.value
  | .phraseAnd p rest => p.value + rest.value

/-- The value of a PHRASE: the product of its immediate constituents. -/
def Phrase.value : Phrase → ℕ
  | .mk n m => n.value * m.value

/-- The value of an M: the second constituent raised to the power of the
first. -/
def M.value : M → ℕ
  | .ten => 10
  | .mk n m => m.value ^ n.value
end

/-! ### Canonical structures -/

/-- The bare tally NUMBER: `n + 1` iterations of *one* — the structures
his rule schema (6) generates before lexicalization compresses them. -/
def Number.tally : ℕ → Number
  | 0 => .one
  | n + 1 => .oneAnd (tally n)

@[simp] theorem Number.value_tally (n : ℕ) : (tally n).value = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tally, value, ih]; omega

/-- Every positive number is expressible — numeral systems name the whole
of ℕ⁺ (his ch. 1 universal). -/
theorem Number.exists_value_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : Number, e.value = n :=
  ⟨tally (n - 1), by simp; omega⟩

/-- The base-power M: `tenPow k` is the M of value `10^(k+1)` — *ten*,
*hundred* (`[two ten]`), *thousand* (`[three ten]`), …. -/
def M.tenPow : ℕ → M
  | 0 => .ten
  | k + 1 => .mk (.tally (k + 1)) .ten

@[simp] theorem M.value_tenPow (k : ℕ) : (tenPow k).value = 10 ^ (k + 1) := by
  cases k with
  | zero => rfl
  | succ k => simp [tenPow, value, Number.value_tally]

theorem M.value_pos : ∀ m : M, 0 < m.value
  | .ten => by norm_num [value]
  | .mk n m => by simpa [value] using pow_pos (value_pos m) n.value

/-- A digit×base PHRASE — *four hundred* as `[[four] [two ten]]` — has
value `m × 10^(k+1)`. -/
theorem Phrase.value_tally_tenPow (m k : ℕ) :
    (Phrase.mk (.tally m) (.tenPow k)).value = (m + 1) * 10 ^ (k + 1) := by
  simp [value]

/-! ### CALCULATE: one depth-indexed operation (his (26)–(29))

The three projection rules order themselves by complexity — addition,
multiplication, exponentiation — and each is the iteration of the one
before, bottoming out in incrementing (adding a tally mark). His (29):
a constituent of depth `d` with immediate constituents `x`, `y` is valued
`CALCULATE d x y`, so the semantic component is a single rule. -/

/-- The depth-indexed arithmetic: depth 1 adds (NUMBER), depth 2
multiplies (PHRASE), depth 3 and beyond exponentiates (M). -/
def calculate : ℕ → ℕ → ℕ → ℕ
  | 1, x, y => x + y
  | 2, x, y => x * y
  | _, x, y => y ^ x

/-- His (29): the three projection rules are `calculate` at the
constituent's depth — NUMBERs at depth 1, PHRASEs at depth 2, Ms at
depth 3. -/
theorem value_eq_calculate (p : Phrase) (rest : Number) (n : Number) (m : M) :
    (Number.phraseAnd p rest).value = calculate 1 p.value rest.value ∧
    (Phrase.mk n m).value = calculate 2 n.value m.value ∧
    (M.mk n m).value = calculate 3 n.value m.value :=
  ⟨rfl, rfl, rfl⟩

/-- The complexity ladder behind the depth-indexing: each operation is
the iteration of the one below — multiplication iterates addition,
exponentiation iterates multiplication. -/
theorem calculate_succ_iterate (x y : ℕ) :
    calculate 2 x y = (calculate 1 y)^[x] 0 ∧
    calculate 3 x y = (calculate 2 y)^[x] 1 := by
  constructor
  · induction x with
    | zero => simp [calculate]
    | succ x ih =>
      simp only [Function.iterate_succ_apply', ← ih, calculate]; ring
  · induction x with
    | zero => simp [calculate]
    | succ x ih =>
      simp only [Function.iterate_succ_apply', ← ih, calculate]; ring

end Syntax.Numeral
