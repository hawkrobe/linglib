/-
# Lower-Bound Numeral Semantics

The lower-bound (or "at least") analysis of number words.

## Core Idea

"Two Fs" means "at least two Fs" — the numeral provides a lower bound.
The "exactly" interpretation arises pragmatically via scalar implicature.

## Predictions

1. **Ambiguity**: "two" is true in worlds with 2, 3, 4, ... objects
2. **Implicature**: RSA derives "exactly 2" as pragmatic strengthening
3. **Cancellation**: Implicature can be canceled (e.g., "two or more")
4. **Knowledge effects**: Partial speaker knowledge cancels implicature

## Empirical Support

Goodman & Stuhlmüller (2013) Experiment 2 shows interpretation varies
with speaker knowledge — only possible if there's an implicature to cancel.

## References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
- Levinson, S. (2000). Presumptive Meanings. Chapter 2.
- Goodman & Stuhlmüller (2013). Knowledge and Implicature.
-/

import Linglib.Theories.Montague.Lexicon.Numerals.Theory

namespace Montague.Lexicon.Numerals

-- ============================================================================
-- Lower-Bound Meaning Function
-- ============================================================================

/--
Lower-bound meaning: numeral `w` is true of cardinality `n` iff `n ≥ w.toNat`.

Examples:
- "two" is true of 2, 3, 4, ... (any cardinality ≥ 2)
- "one" is true of 1, 2, 3, ... (any cardinality ≥ 1)
-/
def lowerBoundMeaning (w : NumWord) (n : Nat) : Bool :=
  n ≥ w.toNat

-- ============================================================================
-- The Theory
-- ============================================================================

/--
Lower-bound numeral theory.

"Two" means ≥2. The exact interpretation emerges via scalar implicature.
-/
def LowerBound : NumeralTheory where
  name := "Lower-bound"
  citation := "Horn 1972"
  meaning := lowerBoundMeaning

-- ============================================================================
-- Key Properties
-- ============================================================================

/-- "two" is compatible with both 2 and 3 (ambiguity exists) -/
theorem lowerBound_two_ambiguous :
    LowerBound.compatibleWorlds .two = [2, 3] := by
  native_decide

/-- Lower-bound has ambiguity for "two" (>1 compatible world) -/
theorem lowerBound_two_has_ambiguity :
    LowerBound.hasAmbiguity .two = true := by
  native_decide

/-- "three" entails "two" in lower-bound semantics -/
theorem lowerBound_three_stronger_than_two :
    LowerBound.isStrongerThan .three .two = true := by
  native_decide

/-- "two" entails "one" in lower-bound semantics -/
theorem lowerBound_two_stronger_than_one :
    LowerBound.isStrongerThan .two .one = true := by
  native_decide

/-- Lower-bound semantics is monotonic -/
theorem lowerBound_is_monotonic :
    LowerBound.checkMonotonic = true := by
  native_decide

-- ============================================================================
-- Compatibility Counts
-- ============================================================================

/-- "one" is compatible with 3 worlds (1, 2, 3) -/
theorem lowerBound_one_count : LowerBound.compatibleCount .one = 3 := by
  native_decide

/-- "two" is compatible with 2 worlds (2, 3) -/
theorem lowerBound_two_count : LowerBound.compatibleCount .two = 2 := by
  native_decide

/-- "three" is compatible with 1 world (3) -/
theorem lowerBound_three_count : LowerBound.compatibleCount .three = 1 := by
  native_decide

-- ============================================================================
-- RSA with Lower-Bound Semantics
-- ============================================================================

-- Note: For RSA computations with lower-bound semantics, use:
-- NumeralTheory.runL1 from Theory.lean

-- Verify it works
#eval LowerBound.utterances  -- [one, two, three]
#eval LowerBound.worlds  -- [0, 1, 2, 3]

end Montague.Lexicon.Numerals
