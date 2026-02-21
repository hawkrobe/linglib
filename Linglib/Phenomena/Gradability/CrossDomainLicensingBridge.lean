import Linglib.Theories.Semantics.Events.DimensionBridge
import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Core.Scale
import Linglib.Core.Time

/-!
# Cross-Domain Licensing Agreement Bridge

The showcase theorem: six independent classification systems from different
linguistic subfields all agree on licensing predictions, because they all
route through `LicensingPipeline.isLicensed` → `Boundedness.isLicensed`.

## The Six Sources

| Source               | Type                | Closed variant  | Module            |
|----------------------|---------------------|-----------------|-------------------|
| Scale boundedness    | `Boundedness`       | `.closed`       | Core/Scale        |
| Mereological tag     | `MereoTag`          | `.qua`          | Core/Scale        |
| Telicity             | `Telicity`          | `.telic`        | Events/Aspect     |
| Vendler class        | `VendlerClass`      | `.accomplishment`| Events/Aspect    |
| Interval boundary    | `BoundaryType`      | `.closed`       | Core/Time         |
| Situation boundedness| `SituationBoundedness`| `.bounded`    | Core/Time         |

All six have `LicensingPipeline` instances mapping their closed/open variants
to `Boundedness.closed`/`.open_`, yielding identical licensing predictions.

## References

- Kennedy, C. (2007). Vagueness and grammar.
- Rouillard, V. (2026). Maximal informativity and temporal in-adverbials.
- Krifka, M. (1989). Nominal reference, temporal constitution.
- Zwarts, J. (2005). Prepositional aspect and the algebra of paths.
-/

namespace Phenomena.Gradability.CrossDomainLicensingBridge

open Core.Scale
open Core.Time
open Semantics.Lexical.Adjective
open Semantics.Lexical.Verb.Aspect
open Fragments.English.Predicates.Adjectival

-- ════════════════════════════════════════════════════
-- § 1. Six Sources Agree on "Closed → Licensed"
-- ════════════════════════════════════════════════════

/-- Six classification systems all predict licensing for their "closed" variants. -/
theorem six_sources_agree_closed :
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    LicensingPipeline.isLicensed MereoTag.qua = true ∧
    LicensingPipeline.isLicensed Telicity.telic = true ∧
    LicensingPipeline.isLicensed VendlerClass.accomplishment = true ∧
    LicensingPipeline.isLicensed Interval.BoundaryType.closed = true ∧
    LicensingPipeline.isLicensed SituationBoundedness.bounded = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. Six Sources Agree on "Open → Blocked"
-- ════════════════════════════════════════════════════

/-- Six classification systems all predict blocking for their "open" variants. -/
theorem six_sources_agree_open :
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    LicensingPipeline.isLicensed MereoTag.cum = false ∧
    LicensingPipeline.isLicensed Telicity.atelic = false ∧
    LicensingPipeline.isLicensed VendlerClass.state = false ∧
    LicensingPipeline.isLicensed Interval.BoundaryType.open_ = false ∧
    LicensingPipeline.isLicensed SituationBoundedness.unbounded = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Kennedy–Rouillard Isomorphism at Phenomena Level
-- ════════════════════════════════════════════════════

/-- Kennedy adjective (closed) and Rouillard E-TIA (closed) agree. -/
theorem kennedy_rouillard_agree {max : Nat} {W₁ W₂ : Type*}
    (μ₁ : W₁ → Degree max) (μ₂ : W₂ → ℕ) :
    (adjMIPDomain μ₁ full).licensed =
    (MIPDomain.rouillardETIA μ₂ .closed).licensed := rfl

/-- Adjective licensing and VP licensing use the same reason:
    both derive from `Boundedness.closed.isLicensed`. -/
theorem full_and_accomplishment_same_reason :
    LicensingPipeline.isLicensed full.scaleType =
    LicensingPipeline.isLicensed VendlerClass.accomplishment := rfl

/-- Open adjective ("tall") blocks for the same reason as atelic VP. -/
theorem tall_and_state_same_reason :
    LicensingPipeline.isLicensed tall.scaleType =
    LicensingPipeline.isLicensed VendlerClass.state := rfl

-- ════════════════════════════════════════════════════
-- § 4. Pairwise Pipeline Agreement
-- ════════════════════════════════════════════════════

/-- Achievement = accomplishment (both telic → closed → licensed). -/
theorem achievement_eq_accomplishment :
    LicensingPipeline.isLicensed VendlerClass.achievement =
    LicensingPipeline.isLicensed VendlerClass.accomplishment := rfl

/-- Activity = state (both atelic → open → blocked). -/
theorem activity_eq_state :
    LicensingPipeline.isLicensed VendlerClass.activity =
    LicensingPipeline.isLicensed VendlerClass.state := rfl

/-- SituationBoundedness.bounded = BoundaryType.closed
    (both → Boundedness.closed → licensed). -/
theorem bounded_eq_closedBoundary :
    LicensingPipeline.isLicensed SituationBoundedness.bounded =
    LicensingPipeline.isLicensed Interval.BoundaryType.closed := rfl

end Phenomena.Gradability.CrossDomainLicensingBridge
