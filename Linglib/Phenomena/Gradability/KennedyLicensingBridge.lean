import Linglib.Phenomena.Gradability.Data
import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Core.Scale

/-!
# Kennedy (2007) Adjective Licensing Bridge

Connects the abstract `adjMIPDomain` and `LicensingPipeline` algebra
(Core/Scale) to concrete Fragment entries (`tall`, `full`, `wet`, `dry`)
and Phenomena data (`closurePuzzle`, `completelyModifier`).

## Bridge Structure

1. **Fragment → MIPDomain**: each Fragment entry's `scaleType` determines
   an `MIPDomain`, whose `.licensed` field yields the licensing prediction.

2. **MIPDomain → Data**: the licensing prediction matches the empirical
   patterns recorded in `closurePuzzle` and `completelyModifier`.

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
-- § 1. Fragment → MIPDomain Licensing
-- ════════════════════════════════════════════════════

/-- "tall" (open scale) → MIPDomain blocks degree modification. -/
theorem tall_blocks_completely {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMIPDomain μ tall).licensed = false :=
  openAdj_blocked μ tall rfl

/-- "full" (closed scale) → MIPDomain licenses degree modification. -/
theorem full_licenses_completely {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMIPDomain μ full).licensed = true :=
  closedAdj_licensed μ full rfl

/-- "wet" (lower-bounded) → MIPDomain licenses. -/
theorem wet_licensed {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMIPDomain μ wet).licensed = true := by
  simp only [adjMIPDomain, MIPDomain.kennedyAdjective, MIPDomain.licensed,
        wet, Boundedness.isLicensed]

/-- "dry" (upper-bounded) → MIPDomain licenses. -/
theorem dry_licensed {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMIPDomain μ dry).licensed = true := by
  simp only [adjMIPDomain, MIPDomain.kennedyAdjective, MIPDomain.licensed,
        dry, Boundedness.isLicensed]

-- ════════════════════════════════════════════════════
-- § 2. MIPDomain → Data Bridges
-- ════════════════════════════════════════════════════

/-- The closure puzzle is predicted by MIPDomain:
    closed-scale adjectives license "completely", open-scale ones don't.
    Matches `closurePuzzle.worksWithClosed` / `.worksWithOpen`. -/
theorem closurePuzzle_predicted {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMIPDomain μ full).licensed = closurePuzzle.worksWithClosed ∧
    (adjMIPDomain μ tall).licensed = closurePuzzle.worksWithOpen := by
  exact ⟨closedAdj_licensed μ full rfl, openAdj_blocked μ tall rfl⟩

/-- "completely" works with AGA-max (closed) but not RGA (open).
    `adjMIPDomain` licensing matches `completelyModifier` fields. -/
theorem completely_distribution {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMIPDomain μ full).licensed = completelyModifier.worksWithAGAMax ∧
    (adjMIPDomain μ tall).licensed = completelyModifier.worksWithRGA := by
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

/-- Pipeline agrees with MIPDomain for all four test adjectives. -/
theorem pipeline_agrees_with_mip {max : Nat} {W : Type*} (μ : W → Degree max) :
    LicensingPipeline.isLicensed tall.scaleType = (adjMIPDomain μ tall).licensed ∧
    LicensingPipeline.isLicensed full.scaleType = (adjMIPDomain μ full).licensed ∧
    LicensingPipeline.isLicensed wet.scaleType = (adjMIPDomain μ wet).licensed ∧
    LicensingPipeline.isLicensed dry.scaleType = (adjMIPDomain μ dry).licensed := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [LicensingPipeline.isLicensed, LicensingPipeline.toBoundedness,
          adjMIPDomain, MIPDomain.kennedyAdjective, MIPDomain.licensed,
          tall, full, wet, dry, Boundedness.isLicensed]

end Phenomena.Gradability.KennedyLicensingBridge
