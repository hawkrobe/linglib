import Linglib.Semantics.Conditionals.ConditionalType
import Linglib.Semantics.Conditionals.Marker

/-!
# German Conditional Markers
[lassiter-2025]

Conditional connectives in German and their HC/PC restrictions.

## Markers

- **falls**: HC-only. Implies speaker uncertainty about the antecedent.
- **wenn**: Can mark both HC and PC. Ambiguous between "if" and "when"
  readings.
-/

namespace German.Conditionals

open _root_.Conditionals (ConditionalMarker ConditionalMarkerType)

/-- German falls: HC-only conditional marker.

    Implies speaker uncertainty; unacceptable in premise conditionals and as the
    main marker of a left-nested conditional ([lassiter-2025], exx. 22, 24). -/
def falls : ConditionalMarker where
  language := "German"
  marker := "falls"
  gloss := "in case"
  markerType := .hcOnly
  notes := "Only hypothetical; implies speaker uncertainty"

/-- German wenn: HC and PC conditional marker.

    Can mark either hypothetical or premise conditionals.
    LNCs with wenn are acceptable ([lassiter-2025], ex. 23). -/
def wenn : ConditionalMarker where
  language := "German"
  marker := "wenn"
  gloss := "if/when"
  markerType := .both
  notes := "Can mark either HC or PC"

end German.Conditionals
