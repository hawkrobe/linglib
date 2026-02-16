import Linglib.Core.Roundness
import Mathlib.Data.Rat.Defs

/-!
# Pragmatic Halo and Precision Modes

Rounding semantics for numeral imprecision (Lasersohn 1999, Krifka 2007, Kao et al. 2014).
Round numbers (100, 1000) are interpreted imprecisely; sharp numbers (103, 1001)
are interpreted precisely. This is the "pragmatic halo" effect.

## References

- Lasersohn, P. (1999). Pragmatic halos. Language 75(3): 522-551.
- Krifka, M. (2007). Approximate interpretation of number words.
- Kao et al. (2014). Nonliteral understanding of number words. PNAS.
- Woodin, Winter & Bhatt (2024). Numeral frequency and roundness.
-/

namespace Semantics.Lexical.Numeral.Precision

/-- Precision mode for numeral interpretation (Kao et al. 2014). -/
inductive PrecisionMode where
  | exact       -- f_e(s) = s
  | approximate -- f_a(s) = Round(s)
  deriving Repr, DecidableEq, BEq

/-- Round a rational number to the nearest multiple of `base`. -/
def roundToNearest (n : ℚ) (base : ℚ := 10) : ℚ :=
  if base == 0 then n
  else
    let scaled := n / base
    let rounded := (scaled + 1/2).floor
    rounded * base

/-- Check if a number is "round" (divisible by base). -/
def isRoundNumber (n : ℚ) (base : ℚ := 10) : Bool :=
  roundToNearest n base == n

/-- Rounding equivalence: two values are equivalent if they round to the same number. -/
def roundingEquiv (n₁ n₂ : ℚ) (base : ℚ := 10) : Bool :=
  roundToNearest n₁ base == roundToNearest n₂ base

/-- Project a value according to precision mode. -/
def projectPrecision (mode : PrecisionMode) (n : ℚ) (base : ℚ := 10) : ℚ :=
  match mode with
  | .exact => n
  | .approximate => roundToNearest n base

/-- Check if stated and actual values match under a given precision mode. -/
def matchesPrecision (mode : PrecisionMode) (stated actual : ℚ) (base : ℚ := 10) : Bool :=
  projectPrecision mode stated base == projectPrecision mode actual base

-- ════════════════════════════════════════════════════
-- Adaptive Pragmatic Halo (Woodin et al. 2024, Krifka 2007, Lasersohn 1999)
-- ════════════════════════════════════════════════════

open Core.Roundness in

/-- Adaptive rounding base: rounder numbers get a coarser base.
    Uses `RoundnessGrade` to avoid duplicating score-binning logic. -/
def adaptiveBase (n : Nat) : ℚ :=
  match Core.Roundness.roundnessGrade n with
  | .high =>
    if n % 1000 == 0 then 100
    else 10
  | .moderate => 10
  | .low => 5
  | .none => 1

open Core.Roundness in

/-- Adaptive tolerance: scales a base tolerance by the roundness score. -/
def adaptiveTolerance (n : Nat) (baseTol : ℚ) : ℚ :=
  let score := Core.Roundness.roundnessScore n
  baseTol * (1 + score / 6)

open Core.Roundness in

/-- Pragmatic halo width as a function of roundness score (Lasersohn 1999). -/
def haloWidth (n : Nat) : ℚ :=
  let score := Core.Roundness.roundnessScore n
  let magnitudeFactor : ℚ := if n ≥ 1000 then 50
                              else if n ≥ 100 then 10
                              else if n ≥ 10 then 5
                              else 1
  magnitudeFactor * score / 6

open Core.Roundness in

/-- Infer precision mode from k-ness score.
    roundnessScore ≥ 2 → `.approximate`; roundnessScore < 2 → `.exact`. -/
def inferPrecisionMode (n : Nat) : PrecisionMode :=
  if Core.Roundness.roundnessScore n ≥ 2 then .approximate
  else .exact

-- Verification

#guard inferPrecisionMode 100 == .approximate  -- score 6 ≥ 2
#guard inferPrecisionMode 50 == .approximate   -- score 4 ≥ 2
#guard inferPrecisionMode 110 == .approximate  -- score 2 ≥ 2
#guard inferPrecisionMode 7 == .exact          -- score 0 < 2
#guard inferPrecisionMode 99 == .exact         -- score 0 < 2
#guard inferPrecisionMode 15 == .exact         -- score 1 < 2

/-- Multiples of 10 have adaptive base ≥ 5. -/
theorem adaptive_base_ge_five_of_div10 (n : Nat) (h10 : n % 10 = 0) :
    adaptiveBase n ≥ 5 := by
  unfold adaptiveBase
  have hs := Core.Roundness.score_ge_two_of_div10 n h10
  split
  · split <;> decide
  · decide
  · decide
  · exact absurd ‹_› (Core.Roundness.grade_ne_none_of_score_ge_one n (by omega))

end Semantics.Lexical.Numeral.Precision
