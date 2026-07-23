import Linglib.Data.Examples.Lassiter2025
import Linglib.Fragments.Japanese.Conditionals
import Linglib.Fragments.German.Conditionals

/-!
# Left-Nested Conditionals: Bridge
[lassiter-2025]

Connects the LNC data from [lassiter-2025]
(`Data/Examples/Lassiter2025.json`) to the conditional marker
typology in `Fragments/{Language}/Conditionals.lean`.

## Main declarations

- `markerOf`: adapter reading a row's `marker` feature into the Fragment's
  `ConditionalMarker` entry
- `acceptable_iff_marker_licenses`: a marker-diagnostic row is acceptable
  iff its marker can mark premise conditionals or non-bare content makes an
  HC reading available
-/

namespace Lassiter2025

open Data.Examples
open Semantics.Conditionals (ConditionalMarker ConditionalMarkerType)

/-- Marker adapter: the Fragment entry for the row's conditional marker. -/
def markerOf (row : LinguisticExample) : Option ConditionalMarker :=
  match row.feature? "marker" with
  | some "nara"  => some Japanese.Conditionals.nara
  | some "ra"    => some Japanese.Conditionals.ra
  | some "wenn"  => some German.Conditionals.wenn
  | some "falls" => some German.Conditionals.falls
  | _ => none

/-- Whether the row's inner conditional has bare (non-modal, non-generic)
    content. Bare content forces the premise-conditional reading, so an
    HC-only marker cannot rescue the LNC. -/
def bareContent (row : LinguisticExample) : Bool :=
  row.feature? "content" == some "bare"

/-- The marker typology's prediction for a row: the LNC is licensed iff the
    marker can mark premise conditionals (`.both`) or non-bare content makes
    an HC reading available. -/
def markerLicenses (row : LinguisticExample) : Option Bool :=
  (markerOf row).map (fun m => m.markerType == .both || !bareContent row)

/-- **Transfer equation**: every marker-diagnostic row is acceptable iff the
    marker typology licenses it — PC-compatible nara/wenn are acceptable as
    the main complementizer of a bare LNC (exx. 18, 23), HC-only -ra and
    falls are not (exx. 19, 24). -/
theorem acceptable_iff_marker_licenses :
    ∀ row ∈ Examples.all, markerOf row ≠ none →
      (row.judgment = .acceptable ↔ markerLicenses row = some true) := by
  decide

end Lassiter2025
