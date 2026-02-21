import Linglib.Theories.Semantics.Conditionals.ConditionalType

/-!
# English Conditional Markers

Conditional connectives in English and their HC/PC restrictions.

## Markers

- **if**: Can mark both HC and PC. Context determines reading.
-/

namespace Fragments.English.Conditionals

open Semantics.Conditionals (ConditionalMarker ConditionalMarkerType)

/-- English if: HC and PC conditional marker.

    Ambiguous between hypothetical and premise readings;
    context determines which interpretation is felicitous. -/
def if_ : ConditionalMarker where
  language := "English"
  marker := "if"
  gloss := "if"
  markerType := .both
  notes := "Ambiguous between HC and PC; context determines reading"

end Fragments.English.Conditionals
