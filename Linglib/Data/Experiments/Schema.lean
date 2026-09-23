module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Experimental results: schema

The primitive values of `Data/Experiments/<Paper>.lean`, the per-paper modules that
`scripts/gen_experiments.py` generates from `Data/Experiments/<Paper>.json`. A paper's own coding
labels (its factors, response types, predictors) become generated enums, and each table it
prints becomes a generated structure with one row per printed line; this file holds only what
every paper shares.

This is data: it imports nothing from `Linglib/` and states no theorems about theories.
A statistic is kept as printed, `Decimal` recording the digits so that `75` and `75.0` differ,
and a study reads it through `Decimal.toRat`. What a study concludes from the numbers (a
prototype, a preference, a significant difference) is a definition in the study, not a stored
label.
-/

@[expose] public section

namespace Data.Experiments

/-- A decimal as printed: the value `mantissa / 10 ^ exponent`, with `exponent` the number of
printed decimal places. -/
structure Decimal where
  mantissa : ℤ
  exponent : ℕ
  deriving DecidableEq, Repr

namespace Decimal

/-- The printed value. -/
def toRat (d : Decimal) : ℚ := d.mantissa / 10 ^ d.exponent

/-- The printed value in hundredths, exact when at most two places are printed: a proportion
printed to two places, in percent. -/
def hundredths (d : Decimal) : ℤ := d.mantissa * 100 / 10 ^ d.exponent

/-- The printed value is the percentage `100 * k / n` rounded to the printed places: the two
differ by at most half a unit in the last printed place. -/
def RoundsPercent (d : Decimal) (k n : ℕ) : Prop :=
  2 * |(100 * 10 ^ d.exponent * k : ℤ) - d.mantissa * n| ≤ n

instance (d : Decimal) (k n : ℕ) : Decidable (d.RoundsPercent k n) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Some count out of `n` rounds to the printed percentage. -/
def AttainablePercent (d : Decimal) (n : ℕ) : Prop := ∃ k : Fin (n + 1), d.RoundsPercent k n

instance (d : Decimal) (n : ℕ) : Decidable (d.AttainablePercent n) :=
  inferInstanceAs (Decidable (∃ _, _))

end Decimal

/-- The sign of a binary feature in the `[+F]` / `[-F]` notation. -/
inductive Sign where
  | plus
  | minus
  deriving DecidableEq, Repr

end Data.Experiments
