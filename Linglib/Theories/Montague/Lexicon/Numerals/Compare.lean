/-
# Numeral Theory Comparison

Infrastructure and theorems for comparing competing numeral semantics.

## Key Comparisons

1. **Ambiguity**: Lower-bound has it, Exact doesn't
2. **Monotonicity**: Lower-bound is monotonic, Exact isn't
3. **Implicature potential**: Only Lower-bound can derive "exactly n"
4. **Empirical fit**: Lower-bound matches G&S 2013 data

## The Decisive Test

Goodman & Stuhlmüller (2013) show that numeral interpretation varies
with speaker knowledge. This is only possible if:
- The literal meaning is weak (allows multiple worlds)
- The strong interpretation is derived (via implicature)
- The implicature can be canceled (with partial knowledge)

Lower-bound meets all three conditions. Exact meets none.

## References

- Goodman & Stuhlmüller (2013). Knowledge and Implicature.
- See RSA/GoodmanStuhlmuller2013.lean for full empirical modeling.
-/

import Linglib.Theories.Montague.Lexicon.Numerals.LowerBound
import Linglib.Theories.Montague.Lexicon.Numerals.Exact

namespace Montague.Lexicon.Numerals

-- ============================================================================
-- Comparison Functions
-- ============================================================================

/--
Do two theories agree on the truth value of utterance `w` in world `n`?
-/
def theoriesAgreeAt (T₁ T₂ : NumeralTheory) (w : NumWord) (n : Nat) : Bool :=
  T₁.meaning w n == T₂.meaning w n

/--
Do two theories agree on utterance `w` across all worlds?
-/
def theoriesAgreeOn (T₁ T₂ : NumeralTheory) (w : NumWord) : Bool :=
  T₁.worlds.all fun n => theoriesAgreeAt T₁ T₂ w n

/--
Find worlds where two theories diverge on utterance `w`.
-/
def divergingWorlds (T₁ T₂ : NumeralTheory) (w : NumWord) : List Nat :=
  T₁.worlds.filter fun n => !theoriesAgreeAt T₁ T₂ w n

/--
Do two theories agree on all utterances in all worlds?
-/
def theoriesEquivalent (T₁ T₂ : NumeralTheory) : Bool :=
  T₁.utterances.all fun w => theoriesAgreeOn T₁ T₂ w

/--
Ambiguity difference: does T₁ have more ambiguity than T₂ for utterance w?
-/
def hasMoreAmbiguity (T₁ T₂ : NumeralTheory) (w : NumWord) : Bool :=
  T₁.compatibleCount w > T₂.compatibleCount w

-- ============================================================================
-- Key Divergence Theorems
-- ============================================================================

/--
**Theories differ on "two"**

Lower-bound: "two" is true at n=2 AND n=3
Exact: "two" is true only at n=2
-/
theorem lowerBound_exact_differ_on_two :
    LowerBound.meaning .two 3 = true ∧ Exact.meaning .two 3 = false := by
  native_decide

/--
The theories diverge at world 3 for "two".
-/
theorem divergence_at_three :
    divergingWorlds LowerBound Exact .two = [3] := by
  native_decide

/--
The theories agree on "two" at world 2.
-/
theorem agreement_at_two :
    theoriesAgreeAt LowerBound Exact .two 2 = true := by
  native_decide

/--
The theories are NOT equivalent overall.
-/
theorem theories_not_equivalent :
    theoriesEquivalent LowerBound Exact = false := by
  native_decide

-- ============================================================================
-- Ambiguity Comparison
-- ============================================================================

/--
Lower-bound has more ambiguity than Exact for "two".
-/
theorem lowerBound_more_ambiguous_two :
    hasMoreAmbiguity LowerBound Exact .two = true := by
  native_decide

/--
Ambiguity counts differ for "two": 2 vs 1.
-/
theorem ambiguity_count_differs :
    LowerBound.compatibleCount .two = 2 ∧ Exact.compatibleCount .two = 1 := by
  native_decide

/--
Lower-bound has ambiguity, Exact doesn't.
-/
theorem ambiguity_presence_differs :
    LowerBound.hasAmbiguity .two = true ∧ Exact.hasAmbiguity .two = false := by
  native_decide

-- ============================================================================
-- Monotonicity Comparison
-- ============================================================================

/--
Lower-bound is monotonic, Exact is not.
-/
theorem monotonicity_differs :
    LowerBound.checkMonotonic = true ∧ Exact.checkMonotonic = false := by
  native_decide

-- ============================================================================
-- Implicature Potential
-- ============================================================================

/--
**Only Lower-Bound Can Support Implicature**

For scalar implicature to arise, we need:
1. Multiple worlds compatible with the literal meaning (ambiguity)
2. A stronger alternative exists on the scale

Lower-bound: "two" compatible with {2, 3}, "three" is stronger → implicature possible
Exact: "two" compatible with {2} only → no ambiguity → no implicature
-/
theorem only_lowerBound_supports_implicature :
    -- Lower-bound has ambiguity AND a stronger alternative
    (LowerBound.compatibleCount .two > 1 ∧ LowerBound.isStrongerThan .three .two)
    ∧
    -- Exact has no ambiguity (so implicature impossible regardless of alternatives)
    (Exact.compatibleCount .two = 1) := by
  native_decide

-- ============================================================================
-- Empirical Adjudication
-- ============================================================================

/-
## Connection to Empirical Data

The decisive empirical test is whether interpretation varies with speaker
knowledge (Goodman & Stuhlmüller 2013, Experiment 2).

**Observation**: When the speaker has partial knowledge, "two" gets a
weaker interpretation (closer to ≥2). With full knowledge, "two" gets
the exact interpretation (=2).

**Lower-bound explanation**:
- Literal meaning: ≥2 (weak, ambiguous)
- With full knowledge: RSA derives "exactly 2" as implicature
- With partial knowledge: implicature canceled, reverts to ≥2

**Exact explanation**: ???
- Literal meaning: =2 (strong, unambiguous)
- There IS no implicature to cancel
- Interpretation should NOT vary with knowledge
- But it DOES vary → contradiction

See RSA/GoodmanStuhlmuller2013.lean for the full formalization.
-/

/--
**Lower-bound is consistent with knowledge-sensitive interpretation.**

Ambiguity is NECESSARY for implicature cancellation.
Lower-bound has ambiguity; Exact doesn't.
-/
theorem lowerBound_consistent_with_cancellation :
    LowerBound.hasAmbiguity .two = true := by
  native_decide

/--
**Exact is INCONSISTENT with knowledge-sensitive interpretation.**

No ambiguity → no implicature → nothing to cancel → no knowledge sensitivity.
But knowledge sensitivity IS observed empirically.
-/
theorem exact_inconsistent_with_cancellation :
    Exact.hasAmbiguity .two = false := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/--
**Summary Theorem: The theories make different empirical predictions.**

| Property            | Lower-bound | Exact   |
|---------------------|-------------|---------|
| "two" ambiguous?    | Yes (2,3)   | No (2)  |
| Implicature?        | Yes         | No      |
| Cancellation?       | Possible    | N/A     |
| Matches G&S 2013?   | Yes         | No      |
-/
theorem summary_comparison :
    -- Ambiguity
    (LowerBound.compatibleCount .two = 2 ∧ Exact.compatibleCount .two = 1)
    ∧
    -- Monotonicity (required for scalar implicature)
    (LowerBound.checkMonotonic = true ∧ Exact.checkMonotonic = false)
    ∧
    -- Divergence point
    (LowerBound.meaning .two 3 = true ∧ Exact.meaning .two 3 = false) := by
  native_decide

-- ============================================================================
-- TODO: Full Connection to Empirical Data
-- ============================================================================

/-
## Future Work

Link to RSA/GoodmanStuhlmuller2013.lean to prove:

```lean
theorem lowerBound_matches_gs2013_data :
    -- RSA with LowerBound predicts knowledge-sensitive interpretation
    sorry

theorem exact_fails_gs2013_data :
    -- RSA with Exact cannot model knowledge-sensitive interpretation
    sorry
```

This requires importing the RSA module and showing that:
1. LowerBound.scenario plugged into the knowledge-state RSA model
   produces the observed pattern (implicature with full access,
   cancellation with partial access)
2. Exact.scenario cannot produce this pattern (no ambiguity to resolve)
-/

end Montague.Lexicon.Numerals
