import Linglib.Theories.Semantics.Conditionals.ConditionalType

/-!
# Japanese Conditional Markers

Conditional morphemes in Japanese and their HC/PC restrictions.

## Markers

- **-ra / -tara**: HC-only. Cannot mark premise conditionals (Iatridou 1991).
- **nara**: Can mark both HC and PC. PC reading available when antecedent
  echoes prior discourse (Lassiter 2025, ex. 15).
- **-(r)eba**: Can mark both HC and PC. Used in Anderson conditionals with
  Non-Past consequent (Mizuno 2024, ex. 4a).
-/

namespace Fragments.Japanese.Conditionals

open Semantics.Conditionals (ConditionalMarker ConditionalMarkerType)

/-- Japanese -ra / -tara: HC-only conditional marker.

    Cannot mark premise conditionals. LNCs with -ra are degraded
    (Lassiter 2025, ex. 16). -/
def ra : ConditionalMarker where
  language := "Japanese"
  marker := "-ra/-tara"
  gloss := "if (hypothetical)"
  markerType := .hcOnly
  notes := "Cannot mark premise conditionals"

/-- Japanese nara: HC and PC conditional marker.

    Can mark premise conditionals. LNCs with nara are acceptable
    (Lassiter 2025, ex. 15). -/
def nara : ConditionalMarker where
  language := "Japanese"
  marker := "nara"
  gloss := "if/given that"
  markerType := .both
  notes := "Can mark premise conditionals (unlike -ra)"

/-- Japanese -(r)eba: HC and PC conditional marker.

    Used in Anderson conditionals (Mizuno 2024). With Non-Past
    consequent, yields Anderson reading; with Past consequent,
    yields counterfactual reading. -/
def eba : ConditionalMarker where
  language := "Japanese"
  marker := "-(r)eba"
  gloss := "if (conditional)"
  markerType := .both
  notes := "Anderson conditionals use this form (Mizuno 2024)"

end Fragments.Japanese.Conditionals
