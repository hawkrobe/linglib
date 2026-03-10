import Mathlib.Data.Rat.Defs

/-!
# Sociolinguistic Variation — Empirical Data
@cite{labov-1966} @cite{labov-2012}

Theory-neutral observations about sociolinguistic variation, specifically
the (ING) variable (*-ing* vs *-in'*) and patterns of style shifting and
social stratification.

## Style shifting

Intra-speaker variation across contexts: the same speaker uses different
variant rates in different situations. The canonical example is Obama's
use of (ING) across casual, careful, and formal speech contexts
(@cite{labov-2012}).

## Social stratification

Inter-speaker variation across social classes: speakers from different
social strata use different variant rates in the same context. The
canonical example is (ING) in New York City (@cite{labov-1966}).

Both patterns are theory-neutral observations that any account of
sociolinguistic variation must capture.
-/

set_option autoImplicit false

namespace Phenomena.SocialMeaning

-- ============================================================================
-- §1. Style shifting: Obama's (ING) across contexts
-- ============================================================================

/-- Observed -in' rates across speech contexts for a single speaker.
    Values are proportions (0–1). -/
structure StyleShiftingDatum where
  casual  : ℚ
  careful : ℚ
  formal  : ℚ

/-- Obama's -in' rates across three contexts (@cite{labov-2012}, p. 22):
    casual (barbecue) ≈ 72%, careful (journalist Q&A) ≈ 33%,
    formal (DNC speech) ≈ 3%. -/
def obama_ING : StyleShiftingDatum where
  casual  := 72/100
  careful := 33/100
  formal  := 3/100

/-- Obama's -in' rate decreases monotonically with formality. -/
theorem obama_ING_monotone :
    obama_ING.casual > obama_ING.careful ∧
    obama_ING.careful > obama_ING.formal := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- §2. Social stratification: (ING) by class in NYC
-- ============================================================================

/-- Observed -in' rates by social class in a single context. -/
structure StratificationDatum where
  upperMiddle : ℚ
  lowerMiddle : ℚ
  working     : ℚ
  lower       : ℚ

/-- (ING) stratification in casual style, NYC (@cite{labov-1966}).
    Approximate rates from the sociolinguistic interview data.
    Lower class ≈ 80%, working class ≈ 50%, lower-middle ≈ 40%,
    upper-middle ≈ 10%. -/
def labov1966_ING_casual : StratificationDatum where
  upperMiddle := 10/100
  lowerMiddle := 40/100
  working     := 50/100
  lower       := 80/100

/-- (ING) stratification is monotone: lower class → more -in'. -/
theorem labov1966_stratification :
    labov1966_ING_casual.lower > labov1966_ING_casual.working ∧
    labov1966_ING_casual.working > labov1966_ING_casual.lowerMiddle ∧
    labov1966_ING_casual.lowerMiddle > labov1966_ING_casual.upperMiddle := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

end Phenomena.SocialMeaning
