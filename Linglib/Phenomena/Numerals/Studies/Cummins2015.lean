import Linglib.Core.Scales.Roundness
import Linglib.Theories.Semantics.Numerals.Precision
import Linglib.Theories.Pragmatics.Implicature.Constraints.NumericalExpressions
import Linglib.Fragments.English.NumeralModifiers
import Mathlib.Data.Rat.Defs

/-!
# @cite{cummins-2015}: k-ness, NSAL, and RSA Cost
@cite{cummins-2015} @cite{kao-etal-2014-hyperbole} @cite{lasersohn-1999} @cite{woodin-etal-2023}

Connects the OT NSAL constraint (`nsalViolations`) and the graded k-ness
roundness model to two downstream pragmatic notions:

1. **NSAL as RSA cost** — the OT violation count, normalised to `[0, 1]`,
   serves as the RSA `cost : U → ℚ` parameter. Round numerals are cheap;
   non-round are expensive.
2. **k-ness as `PrecisionMode` threshold** — `roundnessScore ≥ 2` triggers
   `.approximate` mode, grounding the binary switch used by
   @cite{kao-etal-2014-hyperbole}. The pragmatic halo width
   (@cite{lasersohn-1999}, @cite{krifka-2007}) is also wider for round
   numerals.

The lexical bridge to `Fragments.English.NumeralModifiers` documents the
expected interaction between `requiresRound` modifiers and high k-ness
anchors.
-/

namespace Cummins2015

open Core.Roundness
open Implicature.Constraints.NumericalExpressions
open Semantics.Numerals.Precision

-- ============================================================================
-- § 1: NSAL violations as a normalised RSA cost
-- ============================================================================

/-- NSAL violations as a normalised RSA cost ∈ `[0, 1]`. Bridges the OT NSAL
    constraint to the RSA `cost` parameter: round numerals are "cheap"
    (≈ 0), non-round are "expensive" (≈ 1). The denominator is
    `maxRoundnessScore`, so the codomain is exactly `[0, 1]`. -/
def nsalAsRSACost (n : Nat) : ℚ :=
  nsalViolations n / maxRoundnessScore

/-- Maximally round numerals are free (zero cost). Reduces to the
    `Nat`-level fact `nsalViolations 100 = 0` (closed by `decide`) plus
    `0 / x = 0` over ℚ. -/
theorem maximally_round_free :
    nsalAsRSACost 100 = 0 ∧ nsalAsRSACost 1000 = 0 := by
  unfold nsalAsRSACost
  have h100 : nsalViolations 100 = 0 := by decide
  have h1000 : nsalViolations 1000 = 0 := by decide
  refine ⟨?_, ?_⟩
  · rw [h100]; simp
  · rw [h1000]; simp

/-- Round numerals incur strictly lower RSA cost than non-round ones.
    `Nat`-level reduction of `nsalViolations` followed by `norm_num` over ℚ. -/
theorem round_cheaper_in_rsa :
    nsalAsRSACost 100 < nsalAsRSACost 99 := by
  unfold nsalAsRSACost maxRoundnessScore
  have h100 : nsalViolations 100 = 0 := by decide
  have h99 : nsalViolations 99 = 6 := by decide
  rw [h100, h99]
  norm_num

-- ============================================================================
-- § 2: k-ness grounds Kao et al.'s `PrecisionMode`
-- ============================================================================

/-! `inferPrecisionMode` (in `Numerals.Precision`) is defined by
`roundnessScore n ≥ 2 → .approximate`. This subsection records the
grounding theorems for representative numerals plus the general bridge
that *every* multiple of 10 falls in `.approximate` mode. -/

/-- 100 is round (score 6) → `.approximate` mode. -/
theorem precision_100_approximate :
    inferPrecisionMode 100 = .approximate := by decide

/-- 7 is non-round (score 0) → `.exact` mode. -/
theorem precision_7_exact :
    inferPrecisionMode 7 = .exact := by decide

/-- **General bridge.** Every multiple of 10 is interpreted in
    `.approximate` mode. Follows from `score_ge_two_of_div10`: the score is
    at least 2, so the `roundnessScore n ≥ 2` branch of `inferPrecisionMode`
    fires. -/
theorem multipleOf10_implies_approximate (n : Nat) (hr : n % 10 = 0) :
    inferPrecisionMode n = .approximate := by
  unfold inferPrecisionMode
  have hs := Core.Roundness.score_ge_two_of_div10 n hr
  split
  · rfl
  · omega

-- ============================================================================
-- § 3: Wider halo for round numerals
-- ============================================================================

/-- Pragmatic halo width is strictly wider for round numerals (100) than
    for non-round (7) — the quantitative content of @cite{lasersohn-1999}'s
    halo intuition under the k-ness operationalisation. -/
theorem round_wider_halo :
    haloWidth 100 > haloWidth 7 := by
  unfold haloWidth
  have h100 : Core.Roundness.roundnessScore 100 = 6 := by decide
  have h7 : Core.Roundness.roundnessScore 7 = 0 := by decide
  rw [h100, h7]
  norm_num

-- ============================================================================
-- § 4: Fragment bridge — tolerance modifiers do not formally require roundness
-- ============================================================================

/-- The lexical entry for "approximately" carries `requiresRound = false`.
    @cite{cummins-2015} predicts that combinations with low-k anchors are
    *grammatical but marked* — naturalness correlates with k-ness rather than
    being a hard constraint. -/
theorem approximately_tolerates_nonround :
    Fragments.English.NumeralModifiers.approximately.requiresRound = false := rfl

end Cummins2015
