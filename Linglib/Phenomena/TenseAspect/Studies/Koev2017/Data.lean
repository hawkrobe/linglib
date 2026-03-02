/-!
# @cite{koev-2017} Empirical Data @cite{koev-2017}

Theory-neutral data from Koev (2017, *Journal of Semantics* 34(1):1–38).
The Bulgarian evidential (the -l participle in evidential contexts) is
felicitous when the speaker's evidence acquisition is **spatiotemporally
distant** from the described event: either temporally non-overlapping
(standard indirect evidence) or spatially distant (same time, different
place). Direct witness (same time, same place) is infelicitous.

The paper also demonstrates that the evidential contribution is
**not at issue** (projects past negation and modals) and that the speaker
is **fully committed** to the proposition (non-modal analysis, contra
Izvorski 1997).

-/

namespace Phenomena.TenseAspect.Studies.Koev2017.Data

-- ════════════════════════════════════════════════════
-- § 1. Spatiotemporal Overlap Types
-- ════════════════════════════════════════════════════

/-- Whether the described event and the learning event overlap in time. -/
inductive TemporalOverlap where
  | overlapping     -- τ(e) ∩ τ(e') ≠ ∅
  | nonoverlapping  -- τ(e) ∩ τ(e') = ∅
  deriving DecidableEq, Repr, BEq

/-- Whether the described event and the learning event share a location. -/
inductive SpatialRelation where
  | samePlace       -- loc(e) = loc(e')
  | differentPlace  -- loc(e) ≠ loc(e')
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. Evidential Datum Structure
-- ════════════════════════════════════════════════════

/-- An evidential felicity datum from @cite{koev-2017}.
    Each records the spatiotemporal configuration of the described event
    and the learning event, and whether the evidential is felicitous. -/
structure EvidentialDatum where
  /-- Temporal overlap between described and learning events -/
  temporal : TemporalOverlap
  /-- Spatial relation between described and learning events -/
  spatial : SpatialRelation
  /-- Whether the Bulgarian evidential is felicitous in this configuration -/
  evidentialFelicitous : Bool
  /-- Example number in @cite{koev-2017} -/
  exampleNum : String
  deriving Repr, BEq

-- ════════════════════════════════════════════════════
-- § 3. Core △ Data (Koev 2017, §4)
-- ════════════════════════════════════════════════════

/-- (3)/(25a): Standard indirect evidence — speaker was not present when
    the event occurred. Non-overlapping in time, same place. Felicitous. -/
def indirectEvidence : EvidentialDatum where
  temporal := .nonoverlapping
  spatial := .samePlace
  evidentialFelicitous := true
  exampleNum := "25a"

/-- Direct witness — speaker perceived the event as it happened.
    Overlapping in time, same place. Infelicitous. -/
def directWitness : EvidentialDatum where
  temporal := .overlapping
  spatial := .samePlace
  evidentialFelicitous := false
  exampleNum := "25a-control"

/-- (25b): Smoke from chimney — speaker perceives evidence of the event
    from a different location, at the same time. Overlapping in time,
    different place. Felicitous — spatial distance suffices. -/
def smokeFromChimney : EvidentialDatum where
  temporal := .overlapping
  spatial := .differentPlace
  evidentialFelicitous := true
  exampleNum := "25b"

-- ════════════════════════════════════════════════════
-- § 4. Commitment and Projection Data
-- ════════════════════════════════════════════════════

/-- The evidential does not weaken commitment: "EV(p) and I know
    because I was there" is not contradictory (unlike a modal which
    would predict contradiction). @cite{koev-2017}, §3. -/
def commitmentDatum : Bool := true

/-- The evidential contribution projects past negation: "It is not the
    case that Ivan EV-came" presupposes indirect evidence while negating
    the proposition. @cite{koev-2017}, §5. -/
def projectionDatum : Bool := true

-- ════════════════════════════════════════════════════
-- § 5. △ Felicity Generalization
-- ════════════════════════════════════════════════════

/-- △ predicts felicity: the evidential is felicitous iff the described
    event and the learning event are spatiotemporally distant (temporally
    non-overlapping or spatially distant). -/
def trianglePredicts (d : EvidentialDatum) : Bool :=
  match d.temporal, d.spatial with
  | .nonoverlapping, _              => true   -- temporal disjointness suffices
  | _,               .differentPlace => true  -- spatial distance suffices
  | .overlapping,    .samePlace      => false -- no distance → infelicitous

/-- All core data points. -/
def coreData : List EvidentialDatum :=
  [indirectEvidence, directWitness, smokeFromChimney]

-- ════════════════════════════════════════════════════
-- § 6. Data Verification
-- ════════════════════════════════════════════════════

/-- There are 3 core data points. -/
theorem core_count : coreData.length = 3 := rfl

/-- △ correctly predicts felicity for all core data points. -/
theorem triangle_predicts_all :
    coreData.all (fun d => d.evidentialFelicitous == trianglePredicts d) = true := rfl

end Phenomena.TenseAspect.Studies.Koev2017.Data
