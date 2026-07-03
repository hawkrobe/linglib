/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Quantification.Numerals.Roundness
import Linglib.Semantics.Questions.PrecisionProjection
import Linglib.Core.Algebra.Order.ToIntervalMod

/-!
# Pragmatic halo and precision modes

Rounding semantics for numeral imprecision: round numbers (100, 1000) admit
imprecise construals; sharp numbers (103, 1001) do not — [lasersohn-1999]'s
pragmatic halo, [krifka-2007]'s approximate interpretation.

## Main definitions

- `PrecisionMode`, `projectPrecision`, `roundToNearest`: the two meaning
  projections `f_e(s) = s` and `f_a(s) = Round(s)` of
  [kao-etal-2014-hyperbole], with `Round` = round-to-nearest-multiple.
  `Studies/KaoEtAl2014PMFHyperbole.lean` grounds its goal projections in these.
- `haloWidth`, `inferPrecisionMode`: halo width and precision mode as
  functions of the k-ness score (`Roundness.roundnessScore`). Only the
  monotone relationship — rounder numerals carry wider halos and favour
  approximate construal — is motivated by the cited papers
  ([woodin-etal-2023]'s corpus finding); the magnitude constants and the
  score threshold are stipulations of this formalisation.
-/

namespace Semantics.Numerals.Precision

/-- Precision mode for numeral interpretation: which of
[kao-etal-2014-hyperbole]'s two meaning projections applies. -/
inductive PrecisionMode where
  /-- Exact interpretation, `f_e(s) = s`. -/
  | exact
  /-- Approximate interpretation, `f_a(s) = Round(s)`. -/
  | approximate
  deriving Repr, DecidableEq

/-- Round a rational to the nearest multiple of `base` —
[kao-etal-2014-hyperbole]'s `Round` at the default `base = 10`, the
nearest-representative map of the width-`base` bucket partition
(`Core/Algebra/Order/ToIntervalMod.lean`). -/
def roundToNearest (n : ℚ) (base : ℚ := 10) : ℚ :=
  round (n / base) * base

/-- Rounding moves a value by at most half the grain: the imprecision
introduced by `f_a` at base 10 is bounded by 5
(`abs_sub_round_div_zsmul_le`). -/
theorem abs_sub_roundToNearest_le (n : ℚ) : |n - roundToNearest n| ≤ 5 := by
  have h := abs_sub_round_div_zsmul_le (by norm_num : (0 : ℚ) < 10) n
  norm_num [zsmul_eq_mul] at h
  simpa [roundToNearest] using h

/-- Project a value according to precision mode: `f_e` is the identity,
`f_a` rounds to the nearest multiple of `base`. -/
def projectPrecision (mode : PrecisionMode) (n : ℚ) (base : ℚ := 10) : ℚ :=
  match mode with
  | .exact => n
  | .approximate => roundToNearest n base

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

/-- Infer precision mode from the k-ness score: `roundnessScore ≥ 2` yields
`.approximate`. Known idealisation: score-1 numerals (5, 15, 45, …) come out
`.exact` even though imprecise uses of them are attested. -/
def inferPrecisionMode (n : Nat) : PrecisionMode :=
  if Roundness.roundnessScore n ≥ 2 then .approximate else .exact

/-- `PrecisionMode` is the two-point instance of the QUD-layer
`PrecisionProjection` family: `f_e` is `PrecisionProjection.exact`; `f_a`
at grain `g` rounds within the width-`g` grain (the lower representative
on the ℕ scale — [kao-etal-2014-hyperbole]'s `Round` picks the nearest;
same partition, different canonical representative). -/
def PrecisionMode.projection (g : ℕ) : PrecisionMode → PrecisionProjection ℕ
  | .exact => .exact
  | .approximate => .roundTo g

#guard inferPrecisionMode 100 = .approximate  -- score 6 ≥ 2
#guard inferPrecisionMode 50 = .approximate   -- score 5 ≥ 2
#guard inferPrecisionMode 110 = .approximate  -- score 2 ≥ 2
#guard inferPrecisionMode 7 = .exact          -- score 0 < 2
#guard inferPrecisionMode 99 = .exact         -- score 0 < 2
#guard inferPrecisionMode 15 = .exact         -- score 1 < 2 (see caveat above)

end Semantics.Numerals.Precision
