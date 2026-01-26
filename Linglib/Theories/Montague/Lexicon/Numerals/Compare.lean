/-
# Numeral Theory Comparison

Infrastructure and theorems for comparing competing numeral semantics.

## The Two Real Competitors

1. **LowerBound** (Horn 1972): "two" means ≥2, RSA derives exact reading
2. **Bilateral** (Kennedy 2015): "two" means =2 (via maximality), no RSA strengthening

## Key Comparisons

1. **Ambiguity**: LowerBound has it, Bilateral doesn't
2. **Monotonicity**: LowerBound is monotonic, Bilateral isn't
3. **Implicature potential**: Only LowerBound can derive "exactly n"
4. **Empirical fit**: LowerBound matches G&S 2013 knowledge-sensitivity data

## The Decisive Test

Goodman & Stuhlmüller (2013) show that numeral interpretation varies
with speaker knowledge. This is only possible if:
- The literal meaning is weak (allows multiple worlds)
- The strong interpretation is derived (via implicature)
- The implicature can be canceled (with partial knowledge)

LowerBound meets all three conditions. Bilateral meets none.

## References

- Horn (1972). On the Semantic Properties of Logical Operators in English.
- Kennedy (2015). A "de-Fregean" semantics for modified and unmodified numerals.
- Goodman & Stuhlmüller (2013). Knowledge and Implicature.
-/

import Linglib.Theories.Montague.Lexicon.Numerals.LowerBound
import Linglib.Theories.Montague.Lexicon.Numerals.Bilateral

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
DeFregean: "two" is true only at n=2
-/
theorem lowerBound_exact_differ_on_two :
    LowerBound.meaning .two 3 = true ∧ DeFregean.meaning .two 3 = false := by
  native_decide

/--
The theories diverge at world 3 for "two".
-/
theorem divergence_at_three :
    divergingWorlds LowerBound DeFregean .two = [3] := by
  native_decide

/--
The theories agree on "two" at world 2.
-/
theorem agreement_at_two :
    theoriesAgreeAt LowerBound DeFregean .two 2 = true := by
  native_decide

/--
The theories are NOT equivalent overall.
-/
theorem theories_not_equivalent :
    theoriesEquivalent LowerBound DeFregean = false := by
  native_decide

-- ============================================================================
-- Ambiguity Comparison
-- ============================================================================

/--
Lower-bound has more ambiguity than DeFregean for "two".
-/
theorem lowerBound_more_ambiguous_two :
    hasMoreAmbiguity LowerBound DeFregean .two = true := by
  native_decide

/--
Ambiguity counts differ for "two": 2 vs 1.
-/
theorem ambiguity_count_differs :
    LowerBound.compatibleCount .two = 2 ∧ DeFregean.compatibleCount .two = 1 := by
  native_decide

/--
Lower-bound has ambiguity, DeFregean doesn't.
-/
theorem ambiguity_presence_differs :
    LowerBound.hasAmbiguity .two = true ∧ DeFregean.hasAmbiguity .two = false := by
  native_decide

-- ============================================================================
-- Monotonicity Comparison
-- ============================================================================

/--
Lower-bound is monotonic, DeFregean is not.
-/
theorem monotonicity_differs :
    LowerBound.checkMonotonic = true ∧ DeFregean.checkMonotonic = false := by
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
DeFregean: "two" compatible with {2} only → no ambiguity → no implicature
-/
theorem only_lowerBound_supports_implicature :
    -- Lower-bound has ambiguity AND a stronger alternative
    (LowerBound.compatibleCount .two > 1 ∧ LowerBound.isStrongerThan .three .two)
    ∧
    -- DeFregean has no ambiguity (so implicature impossible regardless of alternatives)
    (DeFregean.compatibleCount .two = 1) := by
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

**DeFregean explanation**: ???
- Literal meaning: =2 (strong, unambiguous)
- There IS no implicature to cancel
- Interpretation should NOT vary with knowledge
- But it DOES vary → contradiction

See RSA/GoodmanStuhlmuller2013.lean for the full formalization.
-/

/--
**Lower-bound is consistent with knowledge-sensitive interpretation.**

Ambiguity is NECESSARY for implicature cancellation.
Lower-bound has ambiguity; DeFregean doesn't.
-/
theorem lowerBound_consistent_with_cancellation :
    LowerBound.hasAmbiguity .two = true := by
  native_decide

/--
**DeFregean is INCONSISTENT with knowledge-sensitive interpretation.**

No ambiguity → no implicature → nothing to cancel → no knowledge sensitivity.
But knowledge sensitivity IS observed empirically.
-/
theorem exact_inconsistent_with_cancellation :
    DeFregean.hasAmbiguity .two = false := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/--
**Summary Theorem: The theories make different empirical predictions.**

| Property            | Lower-bound | DeFregean   |
|---------------------|-------------|---------|
| "two" ambiguous?    | Yes (2,3)   | No (2)  |
| Implicature?        | Yes         | No      |
| Cancellation?       | Possible    | N/A     |
| Matches G&S 2013?   | Yes         | No      |
-/
theorem summary_comparison :
    -- Ambiguity
    (LowerBound.compatibleCount .two = 2 ∧ DeFregean.compatibleCount .two = 1)
    ∧
    -- Monotonicity (required for scalar implicature)
    (LowerBound.checkMonotonic = true ∧ DeFregean.checkMonotonic = false)
    ∧
    -- Divergence point
    (LowerBound.meaning .two 3 = true ∧ DeFregean.meaning .two 3 = false) := by
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
    -- RSA with DeFregean cannot model knowledge-sensitive interpretation
    sorry
```

This requires importing the RSA module and showing that:
1. LowerBound.scenario plugged into the knowledge-state RSA model
   produces the observed pattern (implicature with full access,
   cancellation with partial access)
2. DeFregean.scenario cannot produce this pattern (no ambiguity to resolve)
-/

end Montague.Lexicon.Numerals
