import Linglib.Core.SocialMeaning
import Mathlib.Data.Rat.Defs

/-!
# @cite{labov-2012} — Dialect Diversity in America: The Politics of
Language Change

University of Virginia Press, 2012 (Page-Barbour Lectures for 2009).
ISBN 978-0-8139-3326-9.

## Obama's (ING) style shifting (Ch. 2, Figure 3)

The centerpiece example of the "hidden consensus" on (ING): even
President Obama adjusts his -in' vs -ing rate across contexts. Labov
observed Obama in three situations of increasing formality:

1. **Casual**: a Father's Day barbecue on the White House lawn,
   chatting with chef Bobby Flay about barbeque technique. 72% -in'.
2. **Careful**: the Father's Day ceremonies that followed, asking and
   answering political questions. 33% -in'.
3. **Formal**: scripted acceptance speech at the Democratic National
   Convention. 3% -in'.

(p. 13): "on figure 3 registers an -in' percentage of 72% for this
occasion. [...] His percentage of -in' falls to 33%. The most formal
context shown is his scripted acceptance speech at the Democratic
National Convention, where we see only 3% -in'."

The monotone decrease (72% > 33% > 3%) is a textbook illustration of
intra-speaker style shifting along the formality dimension. The data
connects to the SMG model in `Burnett2019.lean`, which derives the
directional pattern (cool-guy prefers -in' in casual context, -ing in
careful context) from Bayesian pragmatic reasoning.
-/

set_option autoImplicit false

namespace Labov2012

-- ============================================================================
-- Obama's (ING) rates (Ch. 2, Figure 3)
-- ============================================================================

/-- Three-context style-shifting observation: proportion of -in' usage
    in casual, careful, and formal speech contexts. -/
structure StyleShiftObs where
  casual  : ℚ
  careful : ℚ
  formal  : ℚ

/-- Obama's (ING) rates across three contexts (@cite{labov-2012},
    Ch. 2, Figure 3):
    casual (barbecue) ≈ 72% /in/, careful (journalist Q&A) ≈ 33%,
    formal (DNC speech) ≈ 3%.

    This illustrates intra-speaker style shifting — the same speaker
    adjusts variant rates with contextual formality. -/
def obama_ING : StyleShiftObs where
  casual  := 72/100
  careful := 33/100
  formal  := 3/100

/-- Obama's /in/ rate decreases monotonically with formality. -/
theorem obama_ING_monotone :
    obama_ING.casual > obama_ING.careful ∧
    obama_ING.careful > obama_ING.formal := by
  exact ⟨by native_decide, by native_decide⟩

end Labov2012
