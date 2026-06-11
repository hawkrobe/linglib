import Linglib.Data.Examples.Schema
import Linglib.Semantics.Tense.Reichenbach
import Linglib.Semantics.Tense.Basic
import Linglib.Data.Examples.Sharvit2003

/-!
# [sharvit-2003]: Embedded Tense and Universal Grammar
[sharvit-2003] [abusch-1997] [ogihara-1996]

Sharvit (Linguistic Inquiry 34(4), 2003) observes a cross-linguistic
correlation between (a) the obligatoriness of utterance-time reference
for present-under-past sentences and (b) the availability of a
"vacuous" past tense in complement clauses. She proposes the
**Embeddability Principle (EP)**: any well-formed matrix LF must be
embeddable under an attitude verb. The EP excludes "type 4" languages
(no SOT rule + matrix-indexical present), predicting the attested
typology of SOT/non-SOT and English/Hebrew/Modern Greek.

## Empirical anchors (verified vs PDF)

- (1) "A week ago, John decided that in ten days, at breakfast, he
  would tell his mother that he missed her." — multiply-embedded SOT,
  nonpast + anteriority readings.
- (2) "John believed that Mary was pregnant." — past-under-past,
  both readings.
- (3) "John believed that Mary is pregnant." — present-under-past,
  ONLY double-access reading.
- (4a)/(4b) "Two years ago, Sally found out that Mary was/is pregnant."
  — diagnostic asymmetry from pregnancy-duration mismatch with double
  access.
- (5)/(6) Hebrew non-SOT minimal pair: embedded PRES gives nonpast,
  embedded PAST gives only anteriority.

## Scope of the Reichenbach frames below

The frames cover the embedded-present-under-future shape (close to
Sharvit's (3) but with future matrix). The (R,E)-frame cannot fully
capture present-under-past double-access — see the JSON's `ex3` for
the empirical content. The Hebrew minimal pair (Sharvit's (5)/(6))
lives entirely in the JSON; structurally the past-form and
present-form would produce identical (R,E)-frames so encoding the
contrast as separate Lean defs would be vacuous.

-/

namespace Sharvit2003

open Tense
open Data.Examples (LinguisticExample)

-- ════════════════════════════════════════════════════════════════
-- § Reichenbach frames for embedded present under future
-- ════════════════════════════════════════════════════════════════

/-- Matrix "John will say..." — future tense, perfective. -/
def matrixWillSay : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 3
  eventTime := 3

/-- Embedded present under future "Mary is sick" — sickness at the
    future saying time, R = P relative to the shifted perspective. -/
def embeddedPresentUnderFuture : ReichenbachFrame ℤ :=
  embeddedFrame matrixWillSay 3 3

/-- Matrix frame satisfies `isFuture` (R > P). -/
theorem matrixWillSayIsFuture : matrixWillSay.isFuture := by
  simp only [ReichenbachFrame.isFuture, matrixWillSay]; omega

/-- Embedded present under future: R = P relative to shifted perspective. -/
theorem embeddedPresentUnderFutureIsPresent : embeddedPresentUnderFuture.isPresent := by
  simp only [ReichenbachFrame.isPresent, embeddedPresentUnderFuture, embeddedFrame, matrixWillSay]

end Sharvit2003
