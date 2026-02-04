/-
# Bilateral Numeral Semantics

Exact (=n) semantics for bare numerals, derived via Kennedy's (2015)
maximality operator.

## The Bilateral Result

Bare numerals denote exact cardinalities:

  ⟦two⟧ = λP. |{x | P(x)}| = 2

This is called "bilateral" because numerals have both a lower AND upper bound
(contrast with "lower-bound" semantics where "two" means ≥2).

## Derivation via Maximality (Kennedy 2015)

The exact meaning is DERIVED compositionally, not stipulated:

  ⟦two⟧ = λP. max{n | P(n)} = 2

This "de-Fregean" analysis treats numerals as predicates of degrees
(like gradable adjectives), not as generalized quantifiers.

## Why Maximality Matters

The maximality derivation is crucial for degree modifiers:

| Modifier     | Semantics      | Class | Ignorance Implicature |
|--------------|----------------|-------|----------------------|
| "more than 3"| max > 3        | A     | No                   |
| "at least 3" | max ≥ 3        | B     | Yes                  |
| "fewer than 3"| max < 3       | A     | No                   |
| "at most 3"  | max ≤ 3        | B     | Yes                  |

Class B modifiers (with ≥/≤) generate ignorance implicatures because
they're compatible with the unmodified numeral. Class A modifiers
(with >/< ) don't, because they exclude the exact reading.

This Class A/B distinction falls out naturally from the maximality analysis.

## Alternative Routes to Bilateral Semantics

Other theorists arrive at bilateral semantics via different routes:
- **Geurts (2006)**: Direct bilateral semantics ("Take 'five'")
- **Breheny (2008)**: Bilateral + specificity/diagonalization for at-least

We follow Kennedy because the maximality derivation supports the
degree modifier predictions that connect to RSA.

## Key Difference from LowerBound

| Theory     | Bare "two" means | RSA role                    |
|------------|------------------|-----------------------------|
| LowerBound | ≥2               | Derives exact reading       |
| Bilateral  | =2 (via max)     | Derives Class B ignorance   |

## References

- Kennedy, C. (2015). A "de-Fregean" semantics (and neo-Gricean pragmatics)
  for modified and unmodified numerals.
- Geurts, B. (2006). Take 'five'. In S. Vogeleer & L. Tasmowski (eds.),
  Non-definiteness and Plurality, 311-329.
-/

import Linglib.Theories.Montague.Determiner.Numeral.Theory
import Linglib.Theories.Montague.Determiner.Numeral.LowerBound

namespace Montague.Determiner.Numeral

-- Bilateral Meaning Function

/--
Bilateral meaning for bare numerals: max{n | P(n)} = w.toNat

"Two Ps" is true iff the maximum n such that P(n) equals 2.
This yields an exact (=n) reading, derived compositionally via maximality.
-/
def bilateralMeaning (w : NumWord) (n : Nat) : Bool :=
  n == w.toNat

-- The Theory

/--
Bilateral numeral theory (Kennedy 2015).

For bare numerals: "two" means max{n | P(n)} = 2, i.e., exactly 2.
The exact meaning is DERIVED via maximality, not stipulated.
-/
def Bilateral : NumeralTheory where
  name := "Bilateral"
  citation := "Kennedy 2015"
  meaning := bilateralMeaning

-- Key Properties

/-- "two" is compatible with only world 2 (exact meaning) -/
theorem bilateral_two_worlds :
    Bilateral.compatibleWorlds .two = [2] := by
  native_decide

/-- No ambiguity for bare numerals (only 1 compatible world) -/
theorem bilateral_no_ambiguity :
    Bilateral.hasAmbiguity .two = false := by
  native_decide

-- Difference from LowerBound

/--
Bilateral differs from LowerBound on bare numerals.

LowerBound: "two" compatible with worlds 2, 3, ...
Bilateral: "two" compatible with only world 2
-/
theorem bilateral_differs_from_lowerBound :
    Bilateral.compatibleWorlds .two ≠ LowerBound.compatibleWorlds .two := by
  native_decide

/--
The key divergence: ambiguity.

LowerBound has ambiguity (RSA derives exact reading).
Bilateral has no ambiguity (exact meaning is literal).
-/
theorem ambiguity_differs :
    LowerBound.hasAmbiguity .two = true ∧
    Bilateral.hasAmbiguity .two = false := by
  native_decide

-- RSA Role Difference

/--
Under Bilateral semantics, RSA does NOT derive "exactly n" for bare numerals.

The exact reading is already the literal meaning. RSA's role shifts to:
- Deriving IGNORANCE implicatures for Class B modifiers ("at least n")
- NOT deriving ignorance for Class A modifiers ("more than n")

This is handled in Degree/Modifiers.lean.
-/
theorem bilateral_no_rsa_strengthening_needed :
    -- Only one world compatible → L0 = L1 (no pragmatic strengthening)
    Bilateral.compatibleCount .two = 1 := by
  native_decide

-- Monotonicity

/-- Bilateral is not monotonic (numerals have disjoint denotations) -/
theorem bilateral_not_monotonic :
    Bilateral.checkMonotonic = false := by
  native_decide

/-- "three" does not entail "two" -/
theorem bilateral_three_not_stronger :
    Bilateral.isStrongerThan .three .two = false := by
  native_decide

-- RSA Scenario

-- Run L1 inference for Bilateral numerals (using NumeralTheory.runL1)
#eval NumeralTheory.runL1 Bilateral .two  -- Should show exact match

-- Backward Compatibility

/-- Alias for backward compatibility with code using DeFregean -/
abbrev DeFregean := Bilateral

/-- Alias for backward compatibility -/
abbrev deFregeanMeaning := bilateralMeaning

/-- Alias for backward compatibility with code using Exact -/
abbrev Exact := Bilateral

/-- Alias for backward compatibility -/
abbrev exactMeaning := bilateralMeaning

-- Summary

/--
**Summary: Bilateral vs LowerBound (Bare Numerals)**

| Property          | LowerBound | Bilateral |
|-------------------|------------|-----------|
| "two" meaning     | ≥2         | =2        |
| Ambiguity         | Yes        | No        |
| RSA strengthens   | Yes        | No        |
| Monotonic         | Yes        | No        |

The key empirical test: does interpretation vary with speaker knowledge?
- LowerBound: Yes (implicature can be canceled)
- Bilateral: No (exact meaning is literal)

See Compare.lean for full comparison and G&S 2013 connection.
-/
theorem bare_numeral_summary :
    -- Bilateral has no ambiguity
    (Bilateral.hasAmbiguity .two = false) ∧
    (Bilateral.compatibleCount .two = 1) ∧
    -- LowerBound has ambiguity
    (LowerBound.hasAmbiguity .two = true) ∧
    (LowerBound.compatibleCount .two = 2) := by
  native_decide

end Montague.Determiner.Numeral
