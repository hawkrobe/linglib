import Linglib.Phenomena.Gradability.Studies.Kennedy2007Licensing
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Core.Scales.Scale

/-!
# Gradability Typology Bridge
@cite{kennedy-2007}

Per-entry verification that the string-based typology data in `Data.lean`
matches the Fragment entries in `Fragments/English/Predicates/Adjectival.lean`
and the `LicensingPipeline` predictions from `Core/Scale.lean`.

## Bridge Structure

For each adjective with both a `Data.lean` typology entry and a Fragment
entry, we verify:

1. **Form match**: `tallTypology.adjective = tall.form`
2. **Scale-type consistency**: `tallTypology.scaleType = tall.scaleType`
3. **Licensing agreement**: `LicensingPipeline.isLicensed tall.scaleType`
   matches the degree modifier compatibility from Data.lean

-/

namespace Kennedy2007Typology

open Phenomena.Gradability.Kennedy2007
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
-- § 2. Scale-type Consistency (full Boundedness equality)
-- ════════════════════════════════════════════════════

/-! With `AdjectiveTypologyDatum.scaleType : Boundedness` (refactored
    from the prior Bool-pair encoding in 0.230.437), the consistency
    theorems can now state full `Boundedness` equality between the
    typology data and the Fragment annotation, rather than just
    projecting both onto `.hasMax`. -/

/-- "tall" (open): Data scaleType matches Fragment scaleType. -/
theorem tall_scaleType_consistency :
    tallTypology.scaleType = tall.scaleType := rfl

/-- "full" (closed): Data scaleType matches Fragment scaleType. -/
theorem full_scaleType_consistency :
    fullTypology.scaleType = full.scaleType := rfl

/-- "wet" (lower-bounded): Data scaleType matches Fragment scaleType. -/
theorem wet_scaleType_consistency :
    wetTypology.scaleType = wet.scaleType := rfl

/-- "straight" (closed): Data scaleType matches Fragment scaleType. -/
theorem straight_scaleType_consistency :
    straightTypology.scaleType = straight.scaleType := rfl

/-- "bent" (lower-bounded): Data scaleType matches Fragment scaleType. -/
theorem bent_scaleType_consistency :
    bentTypology.scaleType = bent.scaleType := rfl

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

end Kennedy2007Typology
