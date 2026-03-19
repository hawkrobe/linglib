import Linglib.Phenomena.Gradability.Data
import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Core.Scales.Scale

/-!
# @cite{kennedy-2007} Adjective Licensing Bridge
@cite{kennedy-2007} @cite{kennedy-mcnally-2005}

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

-- ════════════════════════════════════════════════════
-- § 4. Scale Structure → Comparison Class Sensitivity
-- ════════════════════════════════════════════════════

/-! ### Two independent paths to the same prediction

@cite{kennedy-2007}'s scale structure and `PropertyDomain.requiresComparisonClass`
are two independent classifications that converge on the same prediction for
whether an adjective's standard depends on contextual domain information:

- **Scale-structure path** (@cite{kennedy-2007}): `scaleType → interpretiveEconomy
  → PositiveStandard → PositiveStandard.requiresComparisonClass`
  Open scale → contextual **s** → requires "the distribution of objects in some
  domain (a comparison class)" (Kennedy 2007, p. 42)
- **Domain path** (@cite{sedivy-etal-1999}): `dimension.domain →
  PropertyDomain.requiresComparisonClass`
  Size/evaluative/sensory domains → context-sensitive threshold

Note: Kennedy argues (§2.3, p. 16) that the comparison class is descriptively
real but NOT a semantic argument of *pos*. Our `requiresComparisonClass` tracks
whether contextual domain information is needed — compatible with Kennedy's
view that this information feeds into **s** contextually rather than as a
constituent of the logical form.

For every concrete Fragment adjective, the two paths agree. This convergence
is non-trivial: it reflects the empirical fact that open-scale adjectives
tend to belong to context-sensitive domains (size, evaluative), while
closed-scale adjectives tend to belong to context-insensitive domains (state). -/

open Semantics.Degree (interpretiveEconomy PositiveStandard)

/-- "tall": both paths predict CC-dependence. -/
theorem tall_cc_convergence :
    (interpretiveEconomy tall.scaleType).requiresComparisonClass = true ∧
    tall.dimension.domain.requiresComparisonClass = true :=
  ⟨rfl, rfl⟩

/-- "full": both paths predict CC-independence. -/
theorem full_no_cc_convergence :
    (interpretiveEconomy full.scaleType).requiresComparisonClass = false ∧
    full.dimension.domain.requiresComparisonClass = false :=
  ⟨rfl, rfl⟩

/-- "wet": both paths predict CC-independence
    (lower-bounded → endpoint standard; state domain). -/
theorem wet_no_cc_convergence :
    (interpretiveEconomy wet.scaleType).requiresComparisonClass = false ∧
    wet.dimension.domain.requiresComparisonClass = false :=
  ⟨rfl, rfl⟩

/-- "dry": both paths predict CC-independence
    (upper-bounded → endpoint standard; state domain). -/
theorem dry_no_cc_convergence :
    (interpretiveEconomy dry.scaleType).requiresComparisonClass = false ∧
    dry.dimension.domain.requiresComparisonClass = false :=
  ⟨rfl, rfl⟩

end Phenomena.Gradability.KennedyLicensingBridge
