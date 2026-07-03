import Linglib.Semantics.Conditionals.ConditionalType
import Linglib.Semantics.Conditionals.Marker
import Linglib.Semantics.Modality.Exclusion

/-!
# Japanese Conditional Markers
[cao-white-lassiter-2025] [mizuno-2024]

Conditional morphemes in Japanese and their HC/PC restrictions.

## Markers

- **-ra / -tara**: HC-only. Cannot mark premise conditionals.
- **nara**: Can mark both HC and PC. PC reading available when antecedent
  echoes prior discourse ([cao-white-lassiter-2025], ex. 15).
- **-(e)ba**: Can mark both HC and PC — premise use in Anderson conditionals
  ([mizuno-2024], ex. 4a), hypothetical use in FLVs ([mizuno-2024], ex. 9a).
-/

namespace Japanese.Conditionals

open Semantics.Conditionals (ConditionalMarker ConditionalMarkerType)
open Semantics.Modality.Exclusion (XMarkingExponent)

/-- Japanese -ra / -tara: HC-only conditional marker.

    Cannot mark premise conditionals. LNCs with -ra are degraded
    ([cao-white-lassiter-2025], ex. 16). -/
def ra : ConditionalMarker where
  language := "Japanese"
  marker := "-ra/-tara"
  gloss := "if (hypothetical)"
  markerType := .hcOnly
  notes := "Cannot mark premise conditionals"

/-- Japanese nara: HC and PC conditional marker.

    Can mark premise conditionals. LNCs with nara are acceptable
    ([cao-white-lassiter-2025], ex. 15). -/
def nara : ConditionalMarker where
  language := "Japanese"
  marker := "nara"
  gloss := "if/given that"
  markerType := .both
  notes := "Can mark premise conditionals (unlike -ra)"

/-- Japanese -(e)ba ([mizuno-2024], fn 8): attaches to sentence radicals; premise
    use in Andersons (ex. 4a), hypothetical in FLVs (ex. 9a). The Anderson vs
    counterfactual contrast is carried by the consequent's tense, not the marker. -/
def eba : ConditionalMarker where
  language := "Japanese"
  marker := "-(e)ba"
  gloss := "if (conditional)"
  markerType := .both
  notes := "Anderson conditionals use this form (Mizuno 2024, ex. 4a)"

/-- Japanese X-marking: Fake Past -ta ([ogihara-2014], [mizuno-kaufmann-2019];
    [mizuno-2024] ex. 3). -/
def xMarking : Option XMarkingExponent := some ⟨"-ta", [.past]⟩

end Japanese.Conditionals
