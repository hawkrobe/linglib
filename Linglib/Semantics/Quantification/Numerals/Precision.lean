/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Quantification.Numerals.Roundness
public import Linglib.Semantics.Degree.Granularity
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.DeriveFintype

/-!
# Pragmatic halo and precision modes

Round numbers such as 100 and 1000 admit imprecise construals and sharp numbers such as 103 do
not, Lasersohn's pragmatic halo and Krifka's approximate interpretation. Kao et al. project a
value either exactly or rounded to the nearest multiple of ten, and here the halo width and the
precision mode of a numeral grow with its roundness score.

## Main definitions

* `Numerals.Precision.projectPrecision`: the exact projection `f_e(s) = s` and the approximate
  projection `f_a(s) = Round(s)`, the nearest multiple `Degree.Granularity.representative`.
* `Numerals.Precision.haloWidth`, `Numerals.Precision.inferPrecisionMode`: the halo width and
  the precision mode of a numeral as functions of its roundness score.

## Implementation notes

Only the monotone relationship, that rounder numerals carry wider halos and favour approximate
construal, is motivated by the corpus finding of Woodin et al.; the magnitude constants and the
score threshold are stipulations.

## References

* [lasersohn-1999]
* [krifka-2007]
* [kao-etal-2014-hyperbole]
* [woodin-etal-2024]
-/

@[expose] public section

namespace Numerals.Precision

/-- A precision mode says which of [kao-etal-2014-hyperbole]'s two meaning projections applies to a
numeral. -/
inductive PrecisionMode where
  /-- Exact interpretation, `f_e(s) = s`. -/
  | exact
  /-- Approximate interpretation, `f_a(s) = Round(s)`. -/
  | approximate
  deriving Repr, DecidableEq, Fintype

/-- Projecting a value by precision mode leaves it unchanged under `f_e` and
rounds it to the nearest multiple of `base` under `f_a`. -/
def projectPrecision (mode : PrecisionMode) (n : ℚ) (base : ℚ := 10) : ℚ :=
  match mode with
  | .exact => n
  | .approximate => Degree.Granularity.representative base n

/-! ### Halo width and precision-mode inference

Stipulated operationalisations over the k-ness score. Making the mode a
function of the numeral alone idealises away the contextual choice of
granularity ([krifka-2007]) and joint probabilistic inference
([kao-etal-2014-hyperbole]); see the caveat on `inferPrecisionMode`. -/

/-- Pragmatic halo width, increasing in the roundness score. The magnitude
factors are stipulated, not paper-derived. -/
def haloWidth (n : Nat) : ℚ :=
  let score := Roundness.roundnessScore n
  let magnitudeFactor : ℚ :=
    if n ≥ 1000 then 50 else if n ≥ 100 then 10 else if n ≥ 10 then 5 else 1
  magnitudeFactor * score / 6

/-- A value falls within a numeral's pragmatic halo. -/
def withinHalo (n : Nat) (q : ℚ) : Prop := |q - (n : ℚ)| ≤ haloWidth n

instance (n : Nat) (q : ℚ) : Decidable (withinHalo n q) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem haloWidth_nonneg (n : Nat) : 0 ≤ haloWidth n := by
  have h : (0 : ℚ) ≤ (Roundness.roundnessScore n : ℚ) := Nat.cast_nonneg _
  simp only [haloWidth]
  split_ifs <;> exact div_nonneg (mul_nonneg (by norm_num) h) (by norm_num)

/-- Infer precision mode from the k-ness score: `roundnessScore ≥ 2` yields
`.approximate`. Known idealisation: score-1 numerals (5, 15, 45, …) come out
`.exact` even though imprecise uses of them are attested. -/
def inferPrecisionMode (n : Nat) : PrecisionMode :=
  if Roundness.roundnessScore n ≥ 2 then .approximate else .exact

/-- Every multiple of 10 is inferred `.approximate`, since its roundness score is at least 2
(`Roundness.score_ge_two_of_div10`). -/
theorem inferPrecisionMode_eq_approximate_of_ten_dvd {n : ℕ} (h : 10 ∣ n) :
    inferPrecisionMode n = .approximate := by
  unfold inferPrecisionMode
  exact ite_eq_left (Roundness.score_ge_two_of_div10 n h)

example : inferPrecisionMode 100 = .approximate := by decide  -- score 6 ≥ 2
example : inferPrecisionMode 50 = .approximate := by decide   -- score 5 ≥ 2
example : inferPrecisionMode 110 = .approximate := by decide  -- score 2 ≥ 2
example : inferPrecisionMode 7 = .exact := by decide          -- score 0 < 2
example : inferPrecisionMode 99 = .exact := by decide         -- score 0 < 2
example : inferPrecisionMode 15 = .exact := by decide  -- score 1 < 2 (see caveat above)

end Numerals.Precision
