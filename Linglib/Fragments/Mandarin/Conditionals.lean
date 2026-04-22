import Linglib.Theories.Semantics.Conditionals.ConditionalType
import Linglib.Theories.Semantics.Conditionals.Marker

/-!
# Mandarin Conditional Markers
@cite{mizuno-2024}

Conditional morphemes in Mandarin and their properties.

## Markers

- **ruguo** (如果): General-purpose conditional marker. Can mark both HC
  and PC. The O-marking/X-marking distinction in Mandarin conditionals is
  not carried by the conditional marker itself but by the presence or
  absence of perfective *le* (了) in the consequent (@cite{mizuno-2024},
  ex. 11–13).
-/

namespace Fragments.Mandarin.Conditionals

open Semantics.Conditionals (ConditionalMarker ConditionalMarkerType)

/-- Mandarin ruguo (如果): general-purpose conditional marker.

    Can mark both hypothetical and premise conditionals. In
    @cite{mizuno-2024}'s Anderson conditional examples (ex. 13a), the
    conditional marker is `ruguo` regardless of whether the consequent
    is O-marked (no final *le*) or X-marked (with #*le*). -/
def ruguo : ConditionalMarker where
  language := "Mandarin"
  marker := "ruguo (如果)"
  gloss := "if"
  markerType := .both
  notes := "X/O marking carried by consequent le, not by conditional marker"

end Fragments.Mandarin.Conditionals
