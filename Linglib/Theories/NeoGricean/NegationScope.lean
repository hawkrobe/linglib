/-
# Negation Scope in Numeral Interpretation

Formalization of the negation scope asymmetry from Horn (1972), following Jespersen.

## The Asymmetry

When numerals combine with negation, two readings arise:

1. **Internal negation** (default): Negates the lower bound
   - "John doesn't have 3 children" → John has fewer than 3 children
   - Negation targets the assertion (≥3)

2. **External negation** (marked, often stressed): Negates the exact reading
   - "John doesn't have THREE children" → John has some other number (maybe more!)
   - Negation targets the enriched meaning (=3)

## Theoretical Significance

This asymmetry supports lower-bound semantics:
- The lower bound (≥n) is part of the assertion → negatable by default
- The exact reading (=n) is pragmatically derived → requires marked construction

With exact semantics, the asymmetry is unexplained:
- If "three" literally means =3, why is "not three" = <3 (not ≠3)?

## References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
- Jespersen, O. (1917). Negation in English and Other Languages.
-/

import Linglib.Theories.Montague.Lexicon.Numerals.LowerBound
import Linglib.Theories.Montague.Lexicon.Numerals.Exact

open Montague.Lexicon.Numerals

namespace NeoGricean

-- ============================================================================
-- Negation Scope Types
-- ============================================================================

/--
Scope of negation with respect to numeral interpretation.

Following Jespersen (cited in Horn 1972), negation can target:
- The lower bound (internal): "not ≥n" = "<n"
- The exact reading (external): "not =n" = "≠n"
-/
inductive NegationScope where
  /-- Internal negation: targets lower bound. "doesn't have 3" = has <3 -/
  | internal
  /-- External negation: targets exact reading. "doesn't have THREE" = has ≠3 -/
  | external
  deriving DecidableEq, Repr

instance : ToString NegationScope where
  toString
    | .internal => "internal"
    | .external => "external"

-- ============================================================================
-- Negated Meanings
-- ============================================================================

/--
Compute the negated meaning under a given scope.

- Internal: ¬(≥n) = <n (negates lower bound)
- External: ¬(=n) = ≠n (negates exact reading)
-/
def negatedMeaning (T : NumeralTheory) (w : NumWord) (scope : NegationScope) (k : Nat) : Bool :=
  match scope with
  | .internal => !(T.meaning w k)  -- ¬(literal meaning)
  | .external => k != w.toNat      -- ¬(exact reading), regardless of theory

/--
Internal negation of lower-bound: "not ≥n" = "<n"
-/
def lowerBound_internal_neg (w : NumWord) (k : Nat) : Bool :=
  k < w.toNat

/--
External negation targets exact reading: "not =n" = "≠n"
-/
def external_neg (w : NumWord) (k : Nat) : Bool :=
  k != w.toNat

-- ============================================================================
-- Theory Predictions
-- ============================================================================

/--
**Lower-bound internal negation gives <n**

"John doesn't have 3 children" (unstressed)
→ ¬(≥3)
→ <3
→ compatible with 0, 1, 2
-/
theorem lowerBound_internal_three :
    (negatedMeaning LowerBound .three .internal 0 = true) ∧
    (negatedMeaning LowerBound .three .internal 1 = true) ∧
    (negatedMeaning LowerBound .three .internal 2 = true) ∧
    (negatedMeaning LowerBound .three .internal 3 = false) := by
  native_decide

/--
**Lower-bound external negation gives ≠n**

"John doesn't have THREE children" (stressed)
→ ¬(=3)
→ compatible with 0, 1, 2, 4, 5, ...
-/
theorem lowerBound_external_three :
    (negatedMeaning LowerBound .three .external 0 = true) ∧
    (negatedMeaning LowerBound .three .external 2 = true) ∧
    (negatedMeaning LowerBound .three .external 3 = false) := by
  native_decide

/--
**The asymmetry is predicted by lower-bound semantics**

Internal negation (default) differs from external negation (marked):
- Internal: worlds where ¬(≥n), i.e., <n
- External: worlds where ≠n

At world 4: internal gives false (4 ≥ 3), external gives true (4 ≠ 3)
-/
theorem negation_asymmetry_at_four :
    negatedMeaning LowerBound .three .internal 4 = false ∧
    negatedMeaning LowerBound .three .external 4 = true := by
  native_decide

-- ============================================================================
-- Exact Semantics Cannot Explain the Asymmetry
-- ============================================================================

/--
**Problem for Exact semantics: No internal/external distinction**

If "three" literally means =3, then negation gives ≠3.
There's no "weaker" lower-bound assertion to negate.

Both scopes collapse to the same meaning.
-/
theorem exact_no_distinction :
    -- In exact semantics, internal = external (both negate =n)
    (negatedMeaning Exact .three .internal 0 = negatedMeaning Exact .three .external 0) ∧
    (negatedMeaning Exact .three .internal 2 = negatedMeaning Exact .three .external 2) ∧
    (negatedMeaning Exact .three .internal 4 = negatedMeaning Exact .three .external 4) := by
  native_decide

/--
**The key divergence: world 4**

Lower-bound: internal at 4 = false, external at 4 = true (DIFFERENT)
Exact: internal at 4 = true, external at 4 = true (SAME)

Empirically, "John doesn't have 3 children" (unstressed) suggests <3, not ≠3.
This requires the internal/external distinction that only lower-bound provides.
-/
theorem divergence_at_world_4 :
    -- Lower-bound distinguishes scopes at world 4
    (negatedMeaning LowerBound .three .internal 4 ≠ negatedMeaning LowerBound .three .external 4)
    ∧
    -- Exact collapses them
    (negatedMeaning Exact .three .internal 4 = negatedMeaning Exact .three .external 4) := by
  native_decide

-- ============================================================================
-- Default vs Marked Readings
-- ============================================================================

/--
The default (unmarked) reading of negated numerals.

Following Jespersen/Horn, the default is internal negation,
which targets the lower bound.
-/
def defaultNegation : NegationScope := .internal

/--
The marked reading requires prosodic emphasis.

"John doesn't have THREE children" (stress on THREE)
targets the pragmatically enriched exact reading.
-/
def markedNegation : NegationScope := .external

/--
**Default interpretation is internal**

"John doesn't have 3 children" (unmarked)
→ Internal negation
→ <3 (not ≥3)
-/
def interpretNegatedNumeral (_T : NumeralTheory) (_w : NumWord) (stressed : Bool) : NegationScope :=
  if stressed then .external else .internal

-- ============================================================================
-- Compatible Worlds Under Negation
-- ============================================================================

/--
Count worlds compatible with negated numeral under given scope.
-/
def compatibleUnderNegation (T : NumeralTheory) (w : NumWord) (scope : NegationScope) : List Nat :=
  T.worlds.filter (negatedMeaning T w scope)

/--
**Lower-bound internal: fewer worlds than external**

"doesn't have 3" (internal): {0, 1, 2}
"doesn't have THREE" (external): {0, 1, 2} (within standard worlds)
-/
theorem lowerBound_negation_worlds :
    compatibleUnderNegation LowerBound .three .internal = [0, 1, 2] ∧
    compatibleUnderNegation LowerBound .three .external = [0, 1, 2] := by
  native_decide

-- Note: In standard worlds [0,1,2,3], both give same result.
-- The difference appears at world 4+.

-- ============================================================================
-- Extended World Analysis
-- ============================================================================

/--
Extended world set to show the full asymmetry.
-/
def extendedWorlds : List Nat := [0, 1, 2, 3, 4, 5]

/--
Filter extended worlds under negation for a given numeral.
-/
def compatibleExtended (w : NumWord) (scope : NegationScope) : List Nat :=
  extendedWorlds.filter fun k =>
    negatedMeaning LowerBound w scope k

/--
**With extended worlds, the asymmetry is clear**

Internal "not 3": {0, 1, 2} (worlds < 3)
External "not THREE": {0, 1, 2, 4, 5} (worlds ≠ 3)
-/
theorem extended_negation_asymmetry :
    compatibleExtended .three .internal = [0, 1, 2] ∧
    compatibleExtended .three .external = [0, 1, 2, 4, 5] := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/--
**Summary: Negation Scope Supports Lower-Bound Semantics**

| Reading     | Form                      | Meaning  | Theory Support |
|-------------|---------------------------|----------|----------------|
| Internal    | "doesn't have 3"          | <3       | Lower-bound    |
| External    | "doesn't have THREE"      | ≠3       | Both           |

The existence of two distinct readings (internal vs external) is
predicted by lower-bound semantics but not by exact semantics.

Empirical fact: Unmarked negation gives <n, not ≠n.
This requires a lower bound to negate.
-/
theorem negation_summary :
    -- Internal and external differ in lower-bound
    (negatedMeaning LowerBound .three .internal 4 = false ∧
     negatedMeaning LowerBound .three .external 4 = true)
    ∧
    -- They collapse in exact
    (negatedMeaning Exact .three .internal 4 = true ∧
     negatedMeaning Exact .three .external 4 = true)
    ∧
    -- Extended worlds show the full pattern
    (compatibleExtended .three .internal = [0, 1, 2] ∧
     compatibleExtended .three .external = [0, 1, 2, 4, 5]) := by
  native_decide

end NeoGricean
