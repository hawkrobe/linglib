import Linglib.Phenomena.Gradability.Data
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Core.Scale

/-!
# Gradability Typology Bridge

Per-entry verification that the string-based typology data in `Data.lean`
matches the Fragment entries in `Fragments/English/Predicates/Adjectival.lean`
and the `LicensingPipeline` predictions from `Core/Scale.lean`.

## Bridge Structure

For each adjective with both a `Data.lean` typology entry and a Fragment
entry, we verify:

1. **Form match**: `tallTypology.adjective = tall.form`
2. **Endpoint consistency**: `tallTypology.hasMaxEndpoint = tall.scaleType.hasMax`
3. **Licensing agreement**: `LicensingPipeline.isLicensed tall.scaleType`
   matches the degree modifier compatibility from Data.lean

## References

- Kennedy, C. (2007). Vagueness and grammar.
-/

namespace Phenomena.Gradability.TypologyBridge

open Fragments.English.Predicates.Adjectival
open Core.Scale

-- ════════════════════════════════════════════════════
-- § 1. Form Match: Data.lean strings = Fragment forms
-- ════════════════════════════════════════════════════

/-- "tall" typology datum matches Fragment form. -/
theorem tall_form_match : tallTypology.adjective = tall.form := rfl

/-- "full" typology datum matches Fragment form. -/
theorem full_form_match : fullTypology.adjective = full.form := rfl

/-- "wet" typology datum matches Fragment form. -/
theorem wet_form_match : wetTypology.adjective = wet.form := rfl

-- ════════════════════════════════════════════════════
-- § 2. Endpoint Consistency
-- ════════════════════════════════════════════════════

/-- "tall" (open): Data says no max endpoint, Fragment scaleType.hasMax agrees. -/
theorem tall_endpoint_consistency :
    tallTypology.hasMaxEndpoint = tall.scaleType.hasMax := rfl

/-- "full" (closed): Data says max endpoint, Fragment scaleType.hasMax agrees. -/
theorem full_endpoint_consistency :
    fullTypology.hasMaxEndpoint = full.scaleType.hasMax := rfl

/-- "wet" (lowerBounded): Data says no max endpoint, Fragment scaleType.hasMax agrees. -/
theorem wet_endpoint_consistency :
    wetTypology.hasMaxEndpoint = wet.scaleType.hasMax := rfl

-- ════════════════════════════════════════════════════
-- § 3. Licensing ↔ Degree Modifier Agreement
-- ════════════════════════════════════════════════════

/-- "tall" (open scale): pipeline blocked = "completely" doesn't work with RGA. -/
theorem tall_completely_agrees :
    LicensingPipeline.isLicensed tall.scaleType =
    completelyModifier.worksWithRGA := rfl

/-- "full" (closed scale): pipeline licensed = "completely" works with AGA-max. -/
theorem full_completely_agrees :
    LicensingPipeline.isLicensed full.scaleType =
    completelyModifier.worksWithAGAMax := rfl

/-- "tall": typology's naturalWithCompletely matches pipeline prediction. -/
theorem tall_completely_from_pipeline :
    tallTypology.naturalWithCompletely =
    LicensingPipeline.isLicensed tall.scaleType := rfl

/-- "full": typology's naturalWithCompletely matches pipeline prediction. -/
theorem full_completely_from_pipeline :
    fullTypology.naturalWithCompletely =
    LicensingPipeline.isLicensed full.scaleType := rfl

-- ════════════════════════════════════════════════════
-- § 4. Threshold Shift ↔ Open Scale
-- ════════════════════════════════════════════════════

/-- "tall" (open): threshold shifts with comparison class.
    Open-scale adjectives are context-sensitive. -/
theorem tall_threshold_shifts :
    tallTypology.thresholdShifts = true ∧ tall.scaleType = .open_ :=
  ⟨rfl, rfl⟩

/-- "full" (closed): threshold does NOT shift.
    Closed-scale adjectives are absolute. -/
theorem full_threshold_stable :
    fullTypology.thresholdShifts = false ∧ full.scaleType = .closed :=
  ⟨rfl, rfl⟩

end Phenomena.Gradability.TypologyBridge
