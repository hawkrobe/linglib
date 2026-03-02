import Linglib.Phenomena.Quantification.Studies.ScontrasPearl2021
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Linglib.Theories.Pragmatics.NeoGricean.NegationScope

/-!
# Numeral Semantics Bridge for @cite{scontras-pearl-2021} @cite{scontras-pearl-2021} @cite{kennedy-2015} @cite{musolino-2004}
@cite{partee-1987}


Connects S&P's `twoNotTruth` truth conditions to linglib's numeral
semantics infrastructure (`maxMeaning` in `Numeral.Semantics`).

## Grounding

The truth conditions in the data file are grounded in `maxMeaning`:
- Exact surface: "exactly 2 didn't jump" = `maxMeaning.eq 2 (4 - w)`
- Exact inverse: "¬(exactly 2 jumped)" = `!(maxMeaning.eq 2 w)`
- At-least surface: "≥2 didn't jump" = `maxMeaning.ge 2 (4 - w)`
- At-least inverse: "¬(≥2 jumped)" = `!(maxMeaning.ge 2 w)`

## Convergent Evidence for Exact Semantics

S&P's computational modeling result (exact semantics required for the 2-of-4
endorsement pattern) converges with:
1. **@cite{kennedy-2015}**: de-Fregean semantics where bare numerals mean =n
2. **@cite{musolino-2004}**: acquisition data — children reject "two" at w=3
3. **Horn's negation-scope asymmetry**: internal negation requires a lower
   bound to negate; under exact semantics, negation targets =n directly,
   collapsing the internal/external distinction
   (see `NeoGricean.exact_no_distinction`)

The tension: S&P argue for exact (to explain endorsement patterns), while
the negation-scope asymmetry argues for lower-bound (to explain the
internal/external distinction). @cite{kennedy-2015} resolves this:
exact is basic, lower-bound is derived via type-shift.
Negation can target either the basic or derived meaning.
-/

set_option autoImplicit false

namespace Phenomena.Quantification.Bridge.NumeralSemanticsBridge

open Phenomena.Quantification.Studies.ScontrasPearl2021
  (JumpOutcome4 ScopeReading NumeralReading twoNotTruth)
open Semantics.Lexical.Numeral (maxMeaning OrderingRel)

-- ============================================================================
-- §1. Grounding Theorems
-- ============================================================================

/-- Exact surface: "exactly two didn't jump" (out of 4) ↔ exactly two jumped.
    Matches `maxMeaning.eq 2` applied to the complement count (4 - w). -/
theorem twoNotExact_surface_matches_maxMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .exact .surface w = maxMeaning .eq 2 (4 - w.toNat) := by
  intro w; cases w <;> rfl

/-- Exact inverse: "¬(exactly two jumped)" ↔ `!(maxMeaning.eq 2 w)`. -/
theorem twoNotExact_inverse_matches_maxMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .exact .inverse w = !(maxMeaning .eq 2 w.toNat) := by
  intro w; cases w <;> rfl

/-- At-least surface: "at least two didn't jump" ↔ at most two jumped.
    Matches `maxMeaning.ge 2` applied to the complement count. -/
theorem twoNotAtLeast_surface_matches_maxMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .atLeast .surface w = maxMeaning .ge 2 (4 - w.toNat) := by
  intro w; cases w <;> rfl

/-- At-least inverse: "¬(at least two jumped)" ↔ `!(maxMeaning.ge 2 w)`. -/
theorem twoNotAtLeast_inverse_matches_maxMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .atLeast .inverse w = !(maxMeaning .ge 2 w.toNat) := by
  intro w; cases w <;> rfl

-- ============================================================================
-- §2. Convergent Evidence
-- ============================================================================

/-- The negation-scope asymmetry collapses under exact semantics:
    internal and external negation of "three" give the same result.
    This is a bridge from `NeoGricean.NegationScope` showing the tension
    between exact semantics (S&P) and lower-bound (Horn). -/
theorem exact_collapses_negation_scope :
    NeoGricean.negatedMeaning Semantics.Lexical.Numeral.Exact .three .internal 4 =
    NeoGricean.negatedMeaning Semantics.Lexical.Numeral.Exact .three .external 4 := by
  native_decide

/-- Lower-bound semantics preserves the negation-scope distinction.
    Internal (default): ¬(≥3) at 4 → false (4 ≥ 3).
    External (marked): ¬(=3) at 4 → true (4 ≠ 3). -/
theorem lowerBound_preserves_negation_scope :
    NeoGricean.negatedMeaning Semantics.Lexical.Numeral.LowerBound .three .internal 4 ≠
    NeoGricean.negatedMeaning Semantics.Lexical.Numeral.LowerBound .three .external 4 := by
  native_decide

/-- Kennedy's resolution: exact meaning is basic, lower-bound is derived
    via type-shift. Both meanings are grammatically available.
    This is verified in `Numeral.Semantics.lowerBound_from_exact_typeshift`. -/
theorem typeshift_resolves_tension :
    Semantics.Lexical.Numeral.typeLower (maxMeaning .eq) 4 2 2 =
    maxMeaning .ge 2 2 := by native_decide

end Phenomena.Quantification.Bridge.NumeralSemanticsBridge
