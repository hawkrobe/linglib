import Linglib.Phenomena.TenseAspect.Studies.Koev2017.Data
import Linglib.Theories.Semantics.Events.SpatiotemporalDistance
import Linglib.Theories.Semantics.Tense.Evidential
import Linglib.Core.Semantics.Presupposition
import Linglib.Fragments.Bulgarian.Evidentials

/-!
# Koev (2017) Bridge Theorems @cite{koev-2017}

Bridge theorems connecting Koev's (2017) spatiotemporal distance analysis
to existing linglib infrastructure, organized around the paper's four
properties (property 6):

- **(i) Spatiotemporal meaning** — △(e, e_l): §§3–4 below
- **(ii) Speaker commitment** — assertion = p, non-modal: §5
- **(iii)–(iv) Not at issue + Projection** — presup projects past negation: §6

Plus structural bridges:
- **△ vs. temporal ordering** — these are independent constraints: §4
- **Bridge to Cumming (2026)** — △ → T ≤ A (downstream evidence): §7
- **Bridge to nfutL** — existing fragment connection: §8

## Central Claim: Learning Events

The paper's deepest contribution is ontological: evidentials introduce a
**learning event** e_l — the event through which the speaker acquired the
reported information. The formal representation (74b):

  ∃e_l ∧ learn_{cs(k)}(e_l, sp(k), p) ∧ τ(e_l) ≤ time(k) ∧ e △ e_l

The learn predicate is subscripted with **cs(k)** (context set), not with
**p** (scope proposition). This is the formal mechanism for not-at-issue
status: the evidential restricts the context set directly (≈ presupposition),
while the assertion commits the speaker to p via DECL (72).

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
-- § 1. Learning Scenarios (Koev 2017, §4)
-- ════════════════════════════════════════════════════

/-- A learning scenario (Koev 2017, §4): the evidential introduces a
    learning event e_l — the event through which the speaker acquired
    the reported information — paired with the described event e.

    The paper's representation (74b):
      ∃e_l ∧ learn_{cs(k)}(e_l, sp(k), p) ∧ τ(e_l) ≤ time(k) ∧ e △ e_l

    ## The cs(k) Subscript

    The `learn` predicate is subscripted with **cs(k)** (the context set at
    discourse move k), not with the scope proposition p. This is the formal
    mechanism for not-at-issue status: the evidential contribution restricts
    the *context set* directly (≈ presupposition in `PrProp.presup`), while
    the assertion commits the speaker to p via DECL (72), which maps to
    `PrProp.assertion`.

    The mapping is:
    - `learn_{cs(k)}(e_l, sp(k), p)` → `PrProp.presup` (restricts cs)
    - `DECL(72): dc^sp(c) ⊆ p` → `PrProp.assertion` (commits to p)

    This explains why the evidential projects past negation (property 6iv):
    `PrProp.neg` preserves `presup` while negating `assertion`.

    ## What's Captured

    - The **event pair** (e, e_l) — the described event and the learning event
    - **△(e, e_l)** — spatiotemporal distance, via `isTemporallyDisjoint` /
      `isSpatiotemporallyDistant` and bridge to `PrProp` via `toEvidentialProp`
    - **The presup/assertion split** — cs(k) subscript → presup, DECL → assertion

    ## What's Not Captured (Future Work)

    - **The learn predicate itself**: We don't model the knowledge-change
      semantics of `learn(e_l, sp(k), p)`. This would require time-indexed
      epistemic states: K_sp(p, t) ∧ ¬K_sp(p, t') for t' < τ(e_l).
    - **Propositional content p**: The structure pairs events but doesn't
      carry the proposition learned. Adding `p : W → Bool` would require
      a world type parameter constraining downstream usage.
    - **Speech time constraint**: τ(e_l) ≤ time(k) ensures the learning
      event is past. This interacts with tense morphology (the L-participle
      is morphologically past) but is not modeled here.
    - **Evidence source typology**: The paper distinguishes reportative,
      inferential, and assumptive evidence (§5) via different learn
      predicates. We collapse these into a single △ constraint. -/
structure LearningScenario (Time : Type*) [LinearOrder Time] where
  /-- The described event (what happened: e.g., Ivan kissing Maria) -/
  described : Ev Time
  /-- The learning event (how the speaker found out: e.g., hearing a report) -/
  learning : Ev Time

/-- △ holds for this scenario (temporal component): the described and
    learning events have non-overlapping temporal traces. -/
def LearningScenario.isTemporallyDisjoint {Time : Type*} [LinearOrder Time]
    (s : LearningScenario Time) : Prop :=
  temporallyDisjoint s.described s.learning

/-- △ holds for this scenario (full spatiotemporal version): temporal
    disjointness OR spatial distance. -/
def LearningScenario.isSpatiotemporallyDistant {Time : Type*} [LinearOrder Time]
    {L : Type*} [DecidableEq L] (loc : Ev Time → L)
    (s : LearningScenario Time) : Prop :=
  spatiotemporallyDistant loc s.described s.learning

/-- Computable temporal △ for ℤ events: ¬(τ(e) overlaps τ(e_l)).
    Since integer comparison is decidable, we can evaluate △ from the
    event structure directly. -/
def LearningScenario.triangleTemporalB (s : LearningScenario ℤ) : Bool :=
  !(s.described.τ.start ≤ s.learning.τ.finish && s.learning.τ.start ≤ s.described.τ.finish)

/-- `triangleTemporalB` agrees with the propositional `isTemporallyDisjoint`:
    the Bool computation and the Prop predicate coincide for ℤ events. -/
theorem LearningScenario.triangleTemporalB_iff (s : LearningScenario ℤ) :
    s.triangleTemporalB = true ↔ s.isTemporallyDisjoint := by
  unfold triangleTemporalB isTemporallyDisjoint temporallyDisjoint Interval.overlaps
  simp only [Ev.τ]
  constructor
  · intro h ⟨h1, h2⟩
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff,
               decide_eq_false_iff_not] at h
    cases h with
    | inl h => exact h h1
    | inr h => exact h h2
  · intro h
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff,
               decide_eq_false_iff_not]
    by_contra hc
    push_neg at hc
    exact h ⟨hc.1, hc.2⟩

/-- Construct a PrProp from a learning scenario, making the
    cs(k) → presup mapping constructive.

    The presupposition is derived from the event structure (△ holds or not),
    and the assertion is the scope proposition p (committed via DECL).
    This is the concrete realization of Koev's (74b):
    - `presup` := △(described, learning) — the evidential's cs(k) contribution
    - `assertion` := p — the scope proposition -/
def LearningScenario.toEvidentialProp (s : LearningScenario ℤ)
    {W : Type*} (p : W → Bool) : PrProp W where
  presup := fun _ => s.triangleTemporalB
  assertion := p

-- ════════════════════════════════════════════════════
-- § 2. Concrete Scenarios
-- ════════════════════════════════════════════════════

/-- Described event: interval [0, 5]. -/
def describedEvent : Ev ℤ := ⟨⟨0, 5, by omega⟩, .action⟩

/-- Learning event (indirect): interval [10, 15] — strictly later. -/
def learningEventIndirect : Ev ℤ := ⟨⟨10, 15, by omega⟩, .state⟩

/-- Learning event (direct witness): interval [2, 4] — overlaps described. -/
def learningEventDirect : Ev ℤ := ⟨⟨2, 4, by omega⟩, .state⟩

/-- Learning event (spatial distance): interval [0, 5] — same time,
    different place (smoke from chimney). -/
def learningEventSpatial : Ev ℤ := ⟨⟨0, 5, by omega⟩, .state⟩

/-- Indirect evidence scenario: described event [0,5], learning event [10,15]. -/
def indirectScenario : LearningScenario ℤ where
  described := describedEvent
  learning := learningEventIndirect

/-- Smoke-from-chimney scenario: described event [0,5], learning event [0,5]
    at a different location. -/
def smokeScenario : LearningScenario ℤ where
  described := describedEvent
  learning := learningEventSpatial

-- ════════════════════════════════════════════════════
-- § 3. Property (i): Spatiotemporal Meaning — △
-- ════════════════════════════════════════════════════

/-- Indirect evidence: described and learning events are temporally
    disjoint — described event [0,5] finished before learning event
    [10,15] started. △ satisfied via temporal disjointness. -/
theorem indirect_temporallyDisjoint :
    temporallyDisjoint indirectScenario.described indirectScenario.learning := by
  unfold temporallyDisjoint Interval.overlaps indirectScenario describedEvent learningEventIndirect
  simp only [Ev.τ]
  omega

/-- Direct witness: described event [0,5] and learning event [2,4] overlap.
    They are NOT temporally disjoint — △ fails (when also co-located). -/
theorem direct_not_disjoint :
    ¬ temporallyDisjoint describedEvent learningEventDirect := by
  unfold temporallyDisjoint Interval.overlaps describedEvent learningEventDirect
  simp only [Ev.τ]
  push_neg
  omega

/-- The smoke scenario events temporally overlap — temporal disjointness
    alone does NOT yield △ here. -/
theorem smoke_temporally_overlapping :
    ¬ temporallyDisjoint smokeScenario.described smokeScenario.learning := by
  unfold temporallyDisjoint Interval.overlaps smokeScenario describedEvent learningEventSpatial
  simp only [Ev.τ]
  push_neg
  omega

/-- Despite temporal overlap, any location function assigning different
    locations to the described and learning events yields △. This captures
    the smoke-from-chimney scenario (§4): spatial distance suffices. -/
theorem smoke_spatiotemporallyDistant
    {L : Type*} [DecidableEq L] (loc : Ev ℤ → L)
    (hdiff : loc smokeScenario.described ≠ loc smokeScenario.learning) :
    spatiotemporallyDistant loc smokeScenario.described smokeScenario.learning :=
  Or.inr hdiff

-- ════════════════════════════════════════════════════
-- § 4. △ vs. Temporal Ordering (Independent Constraints)
-- ════════════════════════════════════════════════════

/-! The paper separates two constraints in (74b):
    - `e △ e_l` : spatiotemporal distance (the **evidential's** contribution)
    - `τ(e) < τ(e_l)` : temporal ordering (the **past tense's** contribution)

    These are independent: △ can hold via spatial distance alone (smoke
    scenario has △ without temporal ordering), and temporal ordering is
    imposed by tense morphology, not the evidential. -/

/-- Temporal ordering: the described event PRECEDES the learning event.
    This is the past tense's contribution, NOT the evidential's.
    Paper (74b): τ(e) < τ(e_l). -/
theorem indirect_tense_ordering :
    indirectScenario.described.τ.precedes indirectScenario.learning.τ := by
  unfold Interval.precedes indirectScenario describedEvent learningEventIndirect
  simp only [Ev.τ]
  omega

/-- The smoke scenario has NO temporal ordering (events are simultaneous),
    yet △ holds via spatial distance. This demonstrates that △ and temporal
    ordering are independent constraints. -/
theorem smoke_no_tense_ordering :
    ¬ smokeScenario.described.τ.precedes smokeScenario.learning.τ := by
  unfold Interval.precedes smokeScenario describedEvent learningEventSpatial
  simp only [Ev.τ]
  omega

-- ════════════════════════════════════════════════════
-- § 5. The Four Properties (Derived from toEvidentialProp)
-- ════════════════════════════════════════════════════

/-! All four properties (property 6) follow from `toEvidentialProp`:

    - **(i) Spatiotemporal meaning**: presup = △(described, learning),
      derived from event structure via `triangleTemporalB`
    - **(ii) Speaker commitment**: assertion = p (non-modal, full commitment)
    - **(iii) Not at issue**: △ is in presup (cs restriction), not assertion
    - **(iv) Projection**: PrProp.neg preserves presup → △ projects past ¬ -/

/-- Property (6i): the presupposition of the constructed PrProp IS the
    △ condition, derived from the event structure. When △ holds (indirect
    evidence), the presupposition is satisfied at every world. -/
theorem indirect_presup_satisfied {W : Type*} (p : W → Bool) (w : W) :
    (indirectScenario.toEvidentialProp p).presup w = true := by
  unfold LearningScenario.toEvidentialProp LearningScenario.triangleTemporalB
         indirectScenario describedEvent learningEventIndirect
  simp only [Ev.τ]
  decide

/-- When △ fails (direct witness), the presupposition fails —
    the evidential sentence is undefined (infelicitous). -/
def directScenario : LearningScenario ℤ where
  described := describedEvent
  learning := learningEventDirect

theorem direct_presup_fails {W : Type*} (p : W → Bool) (w : W) :
    (directScenario.toEvidentialProp p).presup w = false := by
  unfold LearningScenario.toEvidentialProp LearningScenario.triangleTemporalB
         directScenario describedEvent learningEventDirect
  simp only [Ev.τ]
  decide

/-- Property (6ii): the assertion of a scenario's PrProp IS the scope
    proposition. The speaker commits to p, not to a modalized version.
    This holds by construction: DECL (72) maps to `PrProp.assertion`. -/
theorem assertion_is_scope (s : LearningScenario ℤ) {W : Type*} (p : W → Bool) :
    (s.toEvidentialProp p).assertion = p := rfl

/-- A modal evidential (Izvorski 1997) would assert □_e(p) — "p must be
    true given evidence e" — a DIFFERENT proposition from p.

    This is a simplified stub; the full Kratzer-grounded version is
    `Izvorski1997.Bridge.izvorskiEv`, which uses `necessity f g p` as
    the assertion and `!(accessibleWorlds f w).isEmpty` as the presup. -/
def modalEvidential {W : Type*} (evidence : Bool) (must_p : W → Bool) : PrProp W where
  presup := fun _ => evidence
  assertion := must_p

/-- The modal analysis CAN weaken the assertion: there exist
    instantiations where the modal's assertion diverges from the scope
    proposition, while Koev's assertion is always p by construction. -/
theorem modal_can_weaken :
    ∃ (p must_p : Unit → Bool),
      (indirectScenario.toEvidentialProp p).assertion ≠
      (modalEvidential true must_p).assertion := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  intro h
  exact absurd (congr_fun h ()) (by decide)

/-- Property (6iv): the evidential presupposition projects past negation.
    Negating the evidential negates the assertion (p → ¬p) but preserves
    the presupposition (△). This follows from PrProp's general negation
    rule and captures the paper's formalization (78). -/
theorem projection_past_negation (s : LearningScenario ℤ) {W : Type*} (p : W → Bool) :
    (PrProp.neg (s.toEvidentialProp p)).presup = (s.toEvidentialProp p).presup :=
  PrProp.neg_presup _

-- ════════════════════════════════════════════════════
-- § 7. Bridge to Cumming (2026): △ → T ≤ A
-- ════════════════════════════════════════════════════

/-- For the indirect evidence case, temporal disjointness + ordering
    gives isBefore: τ(e).finish ≤ τ(e_l).start. -/
theorem indirect_isBefore :
    indirectScenario.described.τ.isBefore indirectScenario.learning.τ := by
  unfold Interval.isBefore indirectScenario describedEvent learningEventIndirect
  simp only [Ev.τ]
  omega

/-- Construct Cumming's EvidentialFrame from the learning scenario:
    T = τ(e).finish, A = τ(e_l).start. This bridges Koev's event-based
    analysis to Cumming's point-based (S, A, T) frame. -/
def indirectFrame : EvidentialFrame ℤ where
  speechTime := 20
  perspectiveTime := 20
  referenceTime := 20
  eventTime := indirectScenario.described.τ.finish
  acquisitionTime := indirectScenario.learning.τ.start

/-- Cumming's downstream evidence (T ≤ A) holds for the indirect frame —
    the temporal special case of Koev's △. -/
theorem indirect_downstream : downstreamEvidence indirectFrame := by
  unfold downstreamEvidence indirectFrame indirectScenario describedEvent learningEventIndirect
  simp only [Ev.τ]
  omega

-- ════════════════════════════════════════════════════
-- § 8. Bridge to Existing Fragment
-- ════════════════════════════════════════════════════

/-- The existing Bulgarian nfutL entry has EP = downstream (T ≤ A),
    which is the temporal special case of Koev's △: when spatial distance
    is not at play, △ reduces to temporal disjointness, and temporal
    disjointness + described-before-learning gives T ≤ A. -/
theorem nfutL_is_downstream : nfutL.ep = .downstream := rfl

end Phenomena.TenseAspect.Studies.Koev2017.Bridge
