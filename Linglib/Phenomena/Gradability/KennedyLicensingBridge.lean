import Linglib.Phenomena.Gradability.Data
import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Core.Scales.Scale

/-!
# Kennedy (2007) Adjective Licensing Bridge

Connects the abstract `adjMeasure` and `LicensingPipeline` algebra
(Core/Scale) to concrete Fragment entries (`tall`, `full`, `wet`, `dry`)
and Phenomena data (`closurePuzzle`, `completelyModifier`).

## Bridge Structure

1. **Fragment → DirectedMeasure**: each Fragment entry's `scaleType`
   determines a `DirectedMeasure`, whose `.licensed` field yields the
   licensing prediction.

2. **DirectedMeasure → Data**: the licensing prediction matches the
   empirical patterns recorded in `closurePuzzle` and `completelyModifier`.

3. **LicensingPipeline**: the same prediction is available through the
   universal `LicensingPipeline.isLicensed` interface, connecting
   adjective licensing to telicity, path shape, and mereological licensing.

## References

- Kennedy, C. (2007). Vagueness and grammar.
- Kennedy, C. & McNally, L. (2005). Scale structure, degree modification.
-/

namespace Phenomena.Gradability.KennedyLicensingBridge

open Semantics.Lexical.Adjective
open Fragments.English.Predicates.Adjectival
open Core.Scale

-- ════════════════════════════════════════════════════
-- § 1. Fragment → DirectedMeasure Licensing
-- ════════════════════════════════════════════════════

/-- "tall" (open scale) → DirectedMeasure blocks degree modification. -/
theorem tall_blocks_completely {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ tall).licensed = false :=
  openAdj_blocked μ tall rfl

/-- "full" (closed scale) → DirectedMeasure licenses degree modification. -/
theorem full_licenses_completely {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ full).licensed = true :=
  closedAdj_licensed μ full rfl

/-- "wet" (lower-bounded) → DirectedMeasure licenses. -/
theorem wet_licensed {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ wet).licensed = true := by
  simp only [adjMeasure, DirectedMeasure.kennedyAdjective,
        DirectedMeasure.licensed, wet, Boundedness.isLicensed]

/-- "dry" (upper-bounded) → DirectedMeasure licenses. -/
theorem dry_licensed {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ dry).licensed = true := by
  simp only [adjMeasure, DirectedMeasure.kennedyAdjective,
        DirectedMeasure.licensed, dry, Boundedness.isLicensed]

-- ════════════════════════════════════════════════════
-- § 2. DirectedMeasure → Data Bridges
-- ════════════════════════════════════════════════════

/-- The closure puzzle is predicted by DirectedMeasure:
    closed-scale adjectives license "completely", open-scale ones don't.
    Matches `closurePuzzle.worksWithClosed` / `.worksWithOpen`. -/
theorem closurePuzzle_predicted {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ full).licensed = closurePuzzle.worksWithClosed ∧
    (adjMeasure μ tall).licensed = closurePuzzle.worksWithOpen := by
  exact ⟨closedAdj_licensed μ full rfl, openAdj_blocked μ tall rfl⟩

/-- "completely" works with AGA-max (closed) but not RGA (open).
    `adjMeasure` licensing matches `completelyModifier` fields. -/
theorem completely_distribution {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ full).licensed = completelyModifier.worksWithAGAMax ∧
    (adjMeasure μ tall).licensed = completelyModifier.worksWithRGA := by
  exact ⟨closedAdj_licensed μ full rfl, openAdj_blocked μ tall rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. LicensingPipeline Bridges
-- ════════════════════════════════════════════════════

/-- "tall" through the universal pipeline: open_ → blocked. -/
theorem adj_pipeline_tall :
    LicensingPipeline.isLicensed tall.scaleType = false := rfl

/-- "full" through the universal pipeline: closed → licensed. -/
theorem adj_pipeline_full :
    LicensingPipeline.isLicensed full.scaleType = true := rfl

/-- "wet" through the universal pipeline: lowerBounded → licensed. -/
theorem adj_pipeline_wet :
    LicensingPipeline.isLicensed wet.scaleType = true := rfl

/-- "dry" through the universal pipeline: upperBounded → licensed. -/
theorem adj_pipeline_dry :
    LicensingPipeline.isLicensed dry.scaleType = true := rfl

/-- Pipeline agrees with DirectedMeasure for all four test adjectives. -/
theorem pipeline_agrees_with_measure {max : Nat} {W : Type*} (μ : W → Degree max) :
    LicensingPipeline.isLicensed tall.scaleType = (adjMeasure μ tall).licensed ∧
    LicensingPipeline.isLicensed full.scaleType = (adjMeasure μ full).licensed ∧
    LicensingPipeline.isLicensed wet.scaleType = (adjMeasure μ wet).licensed ∧
    LicensingPipeline.isLicensed dry.scaleType = (adjMeasure μ dry).licensed := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [LicensingPipeline.isLicensed, LicensingPipeline.toBoundedness,
          adjMeasure, DirectedMeasure.kennedyAdjective, DirectedMeasure.licensed,
          tall, full, wet, dry, Boundedness.isLicensed]

end Phenomena.Gradability.KennedyLicensingBridge
