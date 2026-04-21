import Linglib.Theories.Semantics.Events.DimensionBridge
import Linglib.Theories.Semantics.Gradability.Theory
import Linglib.Theories.Semantics.Attitudes.EpistemicThreshold
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Core.Scales.Scale
import Linglib.Core.Time.Interval.Basic
import Linglib.Core.Time.Boundedness

/-!
# Cross-Domain Licensing Agreement Bridge
@cite{champollion-2017} @cite{kennedy-2007} @cite{krifka-1989} @cite{krifka-1998} @cite{rouillard-2026} @cite{zwarts-2005} @cite{vendler-1957}

The showcase theorem: six independent classification systems from different
linguistic subfields all agree on licensing predictions, because they all
route through `LicensingPipeline.isLicensed` → `Boundedness.isLicensed`.

## Compositional Chain Architecture

`MereoTag` (QUA/CUM) serves as the canonical bottleneck — all binary domain
classifications route through it, and `MereoTag.toBoundedness` is the single
point where the licensing prediction is made:

```
VendlerClass ─.telicity─→ Telicity ─.toMereoTag─→ MereoTag ─.toBoundedness─→ Boundedness
PathShape ─pathShapeToTelicity─→ Telicity ─.toMereoTag─→ MereoTag ─.toBoundedness─→ Boundedness
SituationBoundedness ─.toMereoTag─→ MereoTag ─.toBoundedness─→ Boundedness
BoundaryType ─.toBoundedness─→ Boundedness (direct — concepts are identical)
EpistemicTag ─.toBoundedness─→ Boundedness (direct — weak mereological link)
```

Each arrow encodes an independently motivated theoretical insight:
- `.telicity`: Vendler classes determine telicity
- `pathShapeToTelicity`: bounded paths create telic VPs
- `.toMereoTag`: telic = quantized
- `.toBoundedness`: quantized = closed scale

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

-/

namespace Phenomena.Gradability.CrossDomainLicensingBridge

open Core (WorldTimeIndex)

open Core.Scale
open Core.Time
open Semantics.Gradability
open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs
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
    (adjMeasure μ₁ full).licensed =
    (DirectedMeasure.rouillardETIA μ₂ .closed).licensed := rfl

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

-- ════════════════════════════════════════════════════
-- § 5. Epistemic Modal Domain (@cite{lassiter-goodman-2017})
-- ════════════════════════════════════════════════════

/-! The epistemic probability scale is closed [0,1] (@cite{kennedy-2007}),
so epistemic adjectives like "certain" license degree modification ("completely
certain") for the same structural reason that "full" does — closed-scale
boundedness routes through `Boundedness.closed → isLicensed = true`.

This connects the seventh licensing source (epistemic modality) to the
existing six, demonstrating that the `LicensingPipeline` unification extends
beyond the adjectival and verbal domains into epistemic modal semantics. -/

open Semantics.Attitudes.EpistemicThreshold (epistemicBoundedness)

/-- Epistemic probability licensing agrees with Kennedy adjective licensing:
    both are `Boundedness.closed → isLicensed = true`.
    "completely certain" is licensed for the same reason as "completely full". -/
theorem epistemic_agrees_with_adj_closed :
    LicensingPipeline.isLicensed epistemicBoundedness =
    LicensingPipeline.isLicensed full.scaleType := rfl

/-- Epistemic licensing agrees with telic VP licensing:
    "completely certain" licensed for the same reason as
    "in an hour" with accomplishments (both closed). -/
theorem epistemic_agrees_with_telic :
    LicensingPipeline.isLicensed epistemicBoundedness =
    LicensingPipeline.isLicensed Telicity.telic := rfl

/-- Epistemic licensing agrees with QUA mereological licensing. -/
theorem epistemic_agrees_with_qua :
    LicensingPipeline.isLicensed epistemicBoundedness =
    LicensingPipeline.isLicensed MereoTag.qua := rfl

end Phenomena.Gradability.CrossDomainLicensingBridge
