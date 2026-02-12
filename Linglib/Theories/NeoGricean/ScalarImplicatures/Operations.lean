/-
# Implicature Operations

Formalization of scalar implicature operations from Horn (1972, §1.22).

## The Three Operations

Horn identifies three operations that speakers can perform on scalar implicatures:

1. **Assert** (reinforce): "P₁(x), but not P₂(x)" / "just/only P₁(x)"
   - Makes the upper-bound implicature explicit
   - Example: "I have two children, not three"

2. **Contradict** (cancel upward): "not just P₁(x), but P₂(x) as well"
   - Denies the upper-bound implicature
   - Example: "I don't have two children, I have three"

3. **Suspend**: "P₁(x), if not P₂(x)" / "at least P₁(x)"
   - Leaves the upper bound undetermined
   - Example: "I have two children, possibly more"

## Insight

These operations target the IMPLICATURE, not the assertion.
- You can suspend "not all" from "some" (implicature)
- You CANNOT suspend "some" from "some" (assertion)

This asymmetry is diagnostic: it shows the upper bound is implicated, not asserted.

## Predictions for Numeral Theories

Lower-bound theory: All three operations valid (there IS an implicature to operate on)
Exact theory: Operations are anomalous (no implicature exists)

## References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English. §1.22, §1.73.
-/

import Linglib.Theories.TruthConditional.Determiner.Numeral.Semantics

open TruthConditional.Determiner.Numeral

namespace NeoGricean

-- Implicature Operations (Horn 1972, §1.22)

/--
Operations on scalar implicatures.

Following Horn (1972), speakers can:
- Assert/reinforce the implicature ("just two", "only two")
- Contradict/cancel the implicature ("not just two, but three")
- Suspend the implicature ("at least two", "two if not more")
-/
inductive ImplicatureOperation where
  /-- Assert the upper-bound implicature: "just/only n" -/
  | assert
  /-- Contradict the implicature: "not just n, but more" -/
  | contradict
  /-- Suspend the implicature: "at least n", "n if not more" -/
  | suspend
  deriving DecidableEq, Repr

instance : ToString ImplicatureOperation where
  toString
    | .assert => "assert"
    | .contradict => "contradict"
    | .suspend => "suspend"

-- Felicity Conditions

/--
An implicature operation is felicitous iff there IS an implicature to operate on.

For numerals, this means:
- The utterance must be ambiguous (compatible with multiple worlds)
- There must be a stronger alternative on the scale

Lower-bound semantics: Operations are felicitous (ambiguity exists)
Exact semantics: Operations are infelicitous (no ambiguity)
-/
def operationFelicitous (T : NumeralTheory) (w : BareNumeral) (_op : ImplicatureOperation) : Bool :=
  -- Need ambiguity (multiple compatible worlds)
  T.hasAmbiguity w
  &&
  -- Need a stronger alternative (for assert/suspend to target)
  match w with
  | .one => T.utterances.contains .two
  | .two => T.utterances.contains .three
  | .three => T.utterances.contains .four
  | .four => T.utterances.contains .five
  | .five => false  -- No stronger standard numeral

/--
Simplified check: is there an implicature to operate on?
-/
def hasImplicatureTarget (T : NumeralTheory) (w : BareNumeral) : Bool :=
  T.hasAmbiguity w

-- Example Sentences (Horn 1972, §1.73)

/--
Example sentences demonstrating the three operations on "two".

These follow Horn's pattern from (1.73):
- Assert: "just two" / "only two" / "two, not three"
- Contradict: "not just two, three" / "not two but three"
- Suspend: "at least two" / "two if not three" / "two or more"
-/
structure OperationExamples where
  numeral : BareNumeral
  assertExamples : List String
  contradictExamples : List String
  suspendExamples : List String

/-- Examples for "two" following Horn (1972) -/
def twoExamples : OperationExamples where
  numeral := .two
  assertExamples := [
    "I have just two children",
    "I have only two children",
    "I have two children, not three"
  ]
  contradictExamples := [
    "I don't have two children, I have three",
    "Not just two, but three children"
  ]
  suspendExamples := [
    "I have at least two children",
    "I have two children, if not three",
    "I have two or more children",
    "I have two children, possibly three"
  ]

-- Theory Predictions

/--
**Lower-bound predicts felicitous operations**

Since "two" means ≥2, it's compatible with both 2 and 3.
This ambiguity licenses implicature operations.
-/
theorem lowerBound_operations_felicitous :
    operationFelicitous LowerBound .two .assert = true ∧
    operationFelicitous LowerBound .two .contradict = true ∧
    operationFelicitous LowerBound .two .suspend = true := by
  native_decide

/--
**Exact predicts infelicitous operations**

Since "two" means =2, it's only compatible with world 2.
No ambiguity → no implicature → nothing to operate on.
-/
theorem exact_operations_infelicitous :
    operationFelicitous Exact .two .assert = false ∧
    operationFelicitous Exact .two .contradict = false ∧
    operationFelicitous Exact .two .suspend = false := by
  native_decide

/--
**The decisive contrast**

The two theories make opposite predictions about whether
"at least two" and "just two" are felicitous modifications.

Empirically, these ARE felicitous → supports Lower-bound.
-/
theorem operation_felicity_differs :
    hasImplicatureTarget LowerBound .two = true ∧
    hasImplicatureTarget Exact .two = false := by
  native_decide

-- Suspension Asymmetry

/--
**Lower-bound suspension is non-redundant**

"At least two" is informative because "two" alone means ≥2 but
IMPLICATES =2. "At least" suspends the implicature.

In exact semantics, "at least two" would be contradictory or meaningless
since "two" already means exactly 2.
-/
def suspensionNonRedundant (T : NumeralTheory) (w : BareNumeral) : Bool :=
  -- Suspension is non-redundant iff there's something to suspend
  T.compatibleCount w > 1

theorem lowerBound_suspension_nonRedundant :
    suspensionNonRedundant LowerBound .two = true := by
  native_decide

theorem exact_suspension_redundant :
    suspensionNonRedundant Exact .two = false := by
  native_decide

-- Reinforcement Analysis (Horn 1972, §1.22)

/--
**Reinforcement is ALWAYS non-redundant**

"Just two" asserts what "two" only implicates.
This is non-redundant precisely because the upper bound is implicated, not asserted.

Contrast with contradiction:
- "I have two children and I don't have all the children" (odd - "all" not implicated)
- "I have two children and I don't have three" (fine - "three" IS implicated)
-/
def reinforcementNonRedundant (T : NumeralTheory) (w : BareNumeral) : Bool :=
  -- Reinforcement ("just n") is non-redundant if there's an implicature
  T.hasAmbiguity w

theorem lowerBound_reinforcement_nonRedundant :
    reinforcementNonRedundant LowerBound .two = true := by
  native_decide

theorem exact_reinforcement_redundant :
    reinforcementNonRedundant Exact .two = false := by
  native_decide

-- Conjunction Redundancy Test (Horn 1972)

/--
**Conjunction Test for Implicature**

Horn uses conjunction redundancy to distinguish implicature from assertion:
- "P and Q" is non-redundant if Q is merely implicated by P
- "P and Q" is redundant if Q is entailed by P

For numerals:
- "I have two children, in fact three" (fine - "not three" was implicated)
- "*I have two children, in fact one" (odd - "at least one" was asserted)
-/
structure ConjunctionTest where
  /-- The base numeral -/
  base : BareNumeral
  /-- The continuation numeral -/
  continuation : BareNumeral
  /-- Is "base, in fact continuation" felicitous? -/
  felicitous : Bool

/--
Upward continuation is felicitous (cancels implicature).
-/
def upwardContinuation (T : NumeralTheory) (base stronger : BareNumeral) : Bool :=
  -- "n, in fact m" where m > n is felicitous iff m was NOT entailed
  -- In lower-bound: "two" doesn't entail "three", so this is fine
  -- We need: base is true at stronger's value, but stronger is "more informative"
  T.meaning base stronger.toNat && T.isStrongerThan stronger base

/--
Downward continuation is infelicitous (contradicts assertion).
-/
def downwardContinuation (T : NumeralTheory) (base weaker : BareNumeral) : Bool :=
  -- "n, in fact m" where m < n is infelicitous iff m contradicts n
  -- In lower-bound: "two" means ≥2, so "in fact one" contradicts
  -- This should be false for well-formed utterances
  T.meaning base weaker.toNat && !T.isStrongerThan base weaker

/--
**Lower-bound predicts asymmetry**

Upward continuation OK (cancels implicature).
Downward continuation bad (contradicts lower bound).
-/
theorem lowerBound_continuation_asymmetry :
    upwardContinuation LowerBound .two .three = true ∧
    downwardContinuation LowerBound .two .one = false := by
  native_decide

-- Connection to RSA

/--
**Why Operations Matter for RSA**

The felicity of implicature operations is evidence that:
1. The literal meaning is weak (compatible with multiple worlds)
2. RSA derives a stronger pragmatic meaning
3. Speakers can manipulate this pragmatic inference

This supports using Lower-bound semantics as the literal meaning
in RSA models of numeral interpretation.
-/
theorem operations_support_rsa_with_lowerBound :
    -- Lower-bound provides the weak literal meaning RSA needs
    LowerBound.hasAmbiguity .two = true ∧
    -- Operations targeting the implicature are felicitous
    operationFelicitous LowerBound .two .suspend = true ∧
    -- This pattern is impossible with exact semantics
    (Exact.hasAmbiguity .two = false ∧ operationFelicitous Exact .two .suspend = false) := by
  native_decide

-- Summary

/--
**Summary: Implicature Operations Distinguish the Theories**

| Operation  | Lower-bound | Exact      |
|------------|-------------|------------|
| Assert     | Felicitous  | Anomalous  |
| Contradict | Felicitous  | Anomalous  |
| Suspend    | Felicitous  | Anomalous  |

The empirical fact that "just two", "at least two", and "not just two"
are all felicitous supports the lower-bound analysis.
-/
theorem operations_summary :
    -- All operations felicitous for Lower-bound
    (operationFelicitous LowerBound .two .assert = true ∧
     operationFelicitous LowerBound .two .contradict = true ∧
     operationFelicitous LowerBound .two .suspend = true)
    ∧
    -- No operations felicitous for Exact
    (operationFelicitous Exact .two .assert = false ∧
     operationFelicitous Exact .two .contradict = false ∧
     operationFelicitous Exact .two .suspend = false) := by
  native_decide

end NeoGricean
