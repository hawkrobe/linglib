import Linglib.Theories.Semantics.Conditionals.ConditionalType

/-!
# German Conditional Markers

Conditional connectives in German and their HC/PC restrictions.

## Markers

- **falls**: HC-only. Implies speaker uncertainty about the antecedent.
- **wenn**: Can mark both HC and PC. Ambiguous between "if" and "when"
  readings.
-/

namespace Fragments.German.Conditionals

open Semantics.Conditionals (ConditionalMarker ConditionalMarkerType)

/-- German falls: HC-only conditional marker.

    Implies speaker uncertainty. LNCs with falls are marginal
    (Lassiter 2025, ex. 21). -/
def falls : ConditionalMarker where
  language := "German"
  marker := "falls"
  gloss := "in case"
  markerType := .hcOnly
  notes := "Only hypothetical; implies speaker uncertainty"

/-- German wenn: HC and PC conditional marker.

    Can mark either hypothetical or premise conditionals.
    LNCs with wenn are acceptable (Lassiter 2025, ex. 20). -/
def wenn : ConditionalMarker where
  language := "German"
  marker := "wenn"
  gloss := "if/when"
  markerType := .both
  notes := "Can mark either HC or PC"

end Fragments.German.Conditionals
