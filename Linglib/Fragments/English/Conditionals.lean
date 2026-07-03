import Linglib.Semantics.Conditionals.ConditionalType
import Linglib.Semantics.Conditionals.Marker
import Linglib.Semantics.Modality.Exclusion

/-!
# English Conditional Markers

Conditional connectives in English and their HC/PC restrictions, and the
language's X-marking exponent ([iatridou-2000], [von-fintel-iatridou-2023]).

## Markers

- **if**: Can mark both HC and PC. Context determines reading.
- **X-marking**: Fake Past, plus woll (would) in the consequent.
-/

namespace English.Conditionals

open Semantics.Conditionals (ConditionalMarker ConditionalMarkerType)
open Semantics.Modality.Exclusion (XMarkingExponent)

/-- English if: HC and PC conditional marker.

    Ambiguous between hypothetical and premise readings;
    context determines which interpretation is felicitous. -/
def if_ : ConditionalMarker where
  language := "English"
  marker := "if"
  gloss := "if"
  markerType := .both
  notes := "Ambiguous between HC and PC; context determines reading"

/-- English X-marking: Fake Past ([iatridou-2000]); the consequent adds woll
    ([von-fintel-iatridou-2023] §2). -/
def xMarking : Option XMarkingExponent := some ⟨"Past", [.past, .future]⟩

end English.Conditionals
