/-
# Exact Numeral Semantics

The exact (or "bilateral") analysis of number words.

## Core Idea

"Two Fs" means "exactly two Fs" — the numeral specifies a precise cardinality.
There is no implicature; the exact meaning is literal.

## Predictions

1. **No ambiguity**: "two" is true only in worlds with exactly 2 objects
2. **No implicature**: Exact interpretation is the literal meaning
3. **No cancellation**: Nothing to cancel — meaning is already maximal
4. **No knowledge effects**: Interpretation shouldn't vary with speaker knowledge

## Empirical Problems

Goodman & Stuhlmüller (2013) Experiment 2 shows interpretation DOES vary
with speaker knowledge. This is unexplainable under exact semantics:
- If "two" literally means exactly 2, there's no implicature
- If there's no implicature, nothing can be canceled
- But cancellation IS observed → contradiction

## References

- Exact semantics is sometimes attributed to formal semantics tradition
- See Geurts (2006) for discussion of bilateral vs. unilateral meanings
- Kennedy (2015) "A 'de-Fregean' semantics for modified and unmodified numerals"
-/

import Linglib.Theories.Montague.Lexicon.Numerals.Theory

namespace Montague.Lexicon.Numerals

-- ============================================================================
-- Exact Meaning Function
-- ============================================================================

/--
Exact meaning: numeral `w` is true of cardinality `n` iff `n = w.toNat`.

Examples:
- "two" is true only of exactly 2
- "one" is true only of exactly 1
-/
def exactMeaning (w : NumWord) (n : Nat) : Bool :=
  n == w.toNat

-- ============================================================================
-- The Theory
-- ============================================================================

/--
Exact numeral theory.

"Two" means exactly 2. No implicature involved.
-/
def Exact : NumeralTheory where
  name := "Exact"
  citation := "cf. Kennedy 2015"
  meaning := exactMeaning

-- ============================================================================
-- Key Properties
-- ============================================================================

/-- "two" is compatible with only world 2 (no ambiguity) -/
theorem exact_two_unambiguous :
    Exact.compatibleWorlds .two = [2] := by
  native_decide

/-- Exact has NO ambiguity for "two" (only 1 compatible world) -/
theorem exact_two_no_ambiguity :
    Exact.hasAmbiguity .two = false := by
  native_decide

/-- "three" does NOT entail "two" in exact semantics -/
theorem exact_three_not_stronger_than_two :
    Exact.isStrongerThan .three .two = false := by
  native_decide

/-- "two" does NOT entail "one" in exact semantics -/
theorem exact_two_not_stronger_than_one :
    Exact.isStrongerThan .two .one = false := by
  native_decide

/-- Exact semantics is NOT monotonic -/
theorem exact_not_monotonic :
    Exact.checkMonotonic = false := by
  native_decide

-- ============================================================================
-- Compatibility Counts
-- ============================================================================

/-- "one" is compatible with 1 world (exactly 1) -/
theorem exact_one_count : Exact.compatibleCount .one = 1 := by
  native_decide

/-- "two" is compatible with 1 world (exactly 2) -/
theorem exact_two_count : Exact.compatibleCount .two = 1 := by
  native_decide

/-- "three" is compatible with 1 world (exactly 3) -/
theorem exact_three_count : Exact.compatibleCount .three = 1 := by
  native_decide

-- ============================================================================
-- The Problem: No Ambiguity Means No Implicature
-- ============================================================================

/--
With exact semantics, numerals have disjoint denotations.
No numeral entails any other.
-/
theorem exact_numerals_disjoint :
    Exact.isStrongerThan .one .two = false ∧
    Exact.isStrongerThan .two .one = false ∧
    Exact.isStrongerThan .two .three = false ∧
    Exact.isStrongerThan .three .two = false := by
  native_decide

/--
**The Core Problem**: Exact semantics cannot model implicature cancellation.

If "two" literally means exactly 2:
- L0("two") assigns probability 1 to world 2, 0 elsewhere
- There is no ambiguity for RSA to resolve
- The "exact" interpretation is not derived — it's stipulated
- Speaker knowledge cannot affect interpretation (nothing to cancel)

But empirically, interpretation DOES vary with knowledge (G&S 2013).
This is only possible if exact interpretation is derived, not literal.
-/
theorem exact_semantics_no_room_for_implicature :
    -- Only one world compatible → no uncertainty → no implicature
    Exact.compatibleCount .two = 1 := by
  native_decide

-- ============================================================================
-- RSA Scenario
-- ============================================================================

/-- The RSA scenario derived from exact semantics -/
def Exact.scenario : RSAScenario := Exact.toScenario

-- Verify it works
#eval Exact.scenario.worlds  -- [0, 1, 2, 3]
#eval Exact.scenario.utterances  -- [one, two, three]

end Montague.Lexicon.Numerals
