import Linglib.Phenomena.TenseAspect.Studies.Koev2017.Data
import Linglib.Theories.Semantics.Events.SpatiotemporalDistance
import Linglib.Theories.Semantics.Tense.Evidential
import Linglib.Core.Semantics.Presupposition
import Linglib.Fragments.Bulgarian.Evidentials

/-!
# Koev (2017) Bridge Theorems @cite{koev-2017}

Bridge theorems connecting Koev's (2017) spatiotemporal distance analysis
to existing linglib infrastructure:

1. **△ felicity verification** — concrete `Ev ℤ` pairs for each
   `EvidentialDatum` verify that `temporallyDisjoint` / `spatiotemporallyDistant`
   match the paper's felicity judgments.
2. **Bridge to Cumming (2026)** — for the standard indirect evidence case,
   temporal disjointness (with described event before learning event) entails
   `isBefore`, connecting to Cumming's T ≤ A.
3. **Projection** — the evidential, modeled as `PrProp.presup`, projects
   past negation: `PrProp.neg_presup`.
4. **Non-modal commitment** — the assertion component is `p` itself (not
   weakened), contra Izvorski (1997).
5. **Bridge to nfutL** — the existing Bulgarian `nfutL` entry's
   `ep = .downstream` is the temporal special case of Koev's △.

## References

- Koev, T. (2017). Evidentiality, learning events, and spatiotemporal
  distance. *Journal of Semantics* 34(1):1–38.
- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175.
- Izvorski, R. (1997). The present perfect as an epistemic modal.
  *SALT* 7:222–239.
-/

namespace Phenomena.TenseAspect.Studies.Koev2017.Bridge

open Core.Time
open Core.Presupposition
open Semantics.Events
open Semantics.Events.SpatiotemporalDistance
open Semantics.Tense.Evidential
open Fragments.Bulgarian.Evidentials

-- ════════════════════════════════════════════════════
-- § 1. Concrete Events for △ Verification
-- ════════════════════════════════════════════════════

/-- Described event: interval [0, 5]. -/
def describedEvent : Ev ℤ := ⟨⟨0, 5, by omega⟩, .action⟩

/-- Learning event (indirect): interval [10, 15] — later than described. -/
def learningEventIndirect : Ev ℤ := ⟨⟨10, 15, by omega⟩, .state⟩

/-- Learning event (direct witness): interval [2, 4] — overlaps described. -/
def learningEventDirect : Ev ℤ := ⟨⟨2, 4, by omega⟩, .state⟩

/-- Learning event (spatial distance): interval [0, 5] — same time,
    different place (smoke from chimney). -/
def learningEventSpatial : Ev ℤ := ⟨⟨0, 5, by omega⟩, .state⟩

-- ════════════════════════════════════════════════════
-- § 2. △ Felicity Verification
-- ════════════════════════════════════════════════════

/-- (25a) Indirect evidence: described and learning events are temporally
    disjoint — described event [0,5] finished before learning event [10,15]
    started. The evidential is felicitous. -/
theorem indirect_temporallyDisjoint :
    temporallyDisjoint describedEvent learningEventIndirect := by
  unfold temporallyDisjoint Interval.overlaps describedEvent learningEventIndirect
  simp only [Ev.τ]
  omega

/-- Direct witness: described event [0,5] and learning event [2,4] overlap.
    The events are NOT temporally disjoint — the evidential is infelicitous
    (when the events are also co-located). -/
theorem direct_overlapping :
    ¬ temporallyDisjoint describedEvent learningEventDirect := by
  unfold temporallyDisjoint Interval.overlaps describedEvent learningEventDirect
  simp only [Ev.τ]
  push_neg
  omega

/-- Location type for the smoke-from-chimney scenario. -/
inductive Place where
  | house
  | street
  deriving DecidableEq

/-- Location function: described event is at the house, spatially-distant
    learning event is on the street. -/
def smokeLoc : Ev ℤ → Place
  | e => if e.runtime.start = 0 && e.sort == .action then .house else .street

/-- (25b) Smoke from chimney: temporally overlapping but spatially distant.
    The evidential is felicitous because △ is satisfied via the spatial
    disjunct. -/
theorem smoke_spatiotemporallyDistant :
    spatiotemporallyDistant smokeLoc describedEvent learningEventSpatial := by
  right
  unfold smokeLoc describedEvent learningEventSpatial
  decide

-- ════════════════════════════════════════════════════
-- § 3. Bridge to Cumming (2026): △ ⇒ T ≤ A
-- ════════════════════════════════════════════════════

/-- For the indirect evidence case, the described event precedes the
    learning event (e₁.τ.finish < e₂.τ.start). -/
theorem indirect_precedes :
    describedEvent.τ.precedes learningEventIndirect.τ := by
  unfold Interval.precedes describedEvent learningEventIndirect
  simp only [Ev.τ]
  omega

/-- The indirect evidence case satisfies isBefore: the described event's
    runtime finishes before the learning event's runtime starts. This
    bridges to Cumming's T ≤ A when we identify T with τ(e).finish and
    A with τ(e_l).start. -/
theorem indirect_isBefore :
    describedEvent.τ.isBefore learningEventIndirect.τ := by
  unfold Interval.isBefore describedEvent learningEventIndirect
  simp only [Ev.τ]
  omega

-- ════════════════════════════════════════════════════
-- § 4. Projection Past Negation
-- ════════════════════════════════════════════════════

/-- Koev's evidential as a presuppositional proposition: the presupposition
    encodes spatiotemporal distance (indirect evidence), the assertion is
    the propositional content. -/
def koevEvidential {W : Type*} (evidence : Bool) (p : W → Bool) : PrProp W where
  presup := fun _ => evidence
  assertion := p

/-- Negation preserves the evidential presupposition: negating a Koev
    evidential proposition negates the assertion but keeps the
    presupposition that the speaker has indirect evidence. -/
theorem evidential_projects_past_negation
    {W : Type*} (evidence : Bool) (p : W → Bool) :
    (PrProp.neg (koevEvidential evidence p)).presup = (koevEvidential evidence p).presup :=
  PrProp.neg_presup _

-- ════════════════════════════════════════════════════
-- § 5. Non-Modal Commitment
-- ════════════════════════════════════════════════════

/-- In Koev's analysis, the assertion of the evidential is the
    proposition itself — full speaker commitment, not weakened by
    a modal. -/
theorem koev_full_commitment
    {W : Type*} (evidence : Bool) (p : W → Bool) :
    (koevEvidential evidence p).assertion = p := rfl

/-- Contrast with a hypothetical modal analysis (Izvorski 1997): the
    assertion would be a DIFFERENT function (some `compatible`), not `p`
    itself. Koev's analysis has `assertion = p` by construction. -/
def izvorskiModal {W : Type*} (evidence : Bool) (compatible : W → Bool) : PrProp W where
  presup := fun _ => evidence
  assertion := compatible

-- ════════════════════════════════════════════════════
-- § 6. Bridge to Existing Fragment
-- ════════════════════════════════════════════════════

/-- The existing Bulgarian nfutL entry has EP = downstream (T ≤ A),
    which is the temporal special case of Koev's △: when the learning
    event is strictly later than the described event, temporal
    disjointness entails T ≤ A. -/
theorem nfutL_is_downstream : nfutL.ep = .downstream := rfl

/-- Construct an EvidentialFrame from the described and learning event
    endpoints: T = τ(e).finish (latest point of described event),
    A = τ(e_l).start (earliest point of learning event). This bridges
    Koev's event-based analysis to Cumming's point-based (S, A, T) frame. -/
def indirectFrame : EvidentialFrame ℤ where
  speechTime := 20
  perspectiveTime := 20
  referenceTime := 20
  eventTime := describedEvent.τ.finish
  acquisitionTime := learningEventIndirect.τ.start

/-- The indirect evidence frame satisfies Cumming's downstream evidence
    constraint: T ≤ A. This is the temporal special case of Koev's △. -/
theorem indirect_downstream : downstreamEvidence indirectFrame := by
  unfold downstreamEvidence indirectFrame describedEvent learningEventIndirect
  simp only [Ev.τ]
  omega

end Phenomena.TenseAspect.Studies.Koev2017.Bridge
