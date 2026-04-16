import Linglib.Theories.Semantics.Tense.AT
import Linglib.Theories.Semantics.Tense.BranchingTime

/-!
# @cite{condoravdi-2002}: Temporal Interpretation of Modals

Condoravdi, C. (2002). Temporal Interpretation of Modals: Modals for the
Present and for the Past. In D. Beaver, S. Kaufmann, B. Clark, & L. Casillas
(Eds.), *The Construction of Meaning* (pp. 59–88). CSLI Publications.

## Core Claims

1. **Uniform modal semantics**: modals for the present and modals for the
   past share a single meaning. No implicit tense under the modal.
2. **Decompositional analysis**: "might have" = MAY(PERF(φ)), not a
   single lexical item MIGHT-HAVE.
3. **Temporal expansion**: modals expand evaluation to `[t,_)` rather
   than shifting it. Forward orientation follows from this for eventive
   predicates; present-or-future for stative predicates.
4. **Scope–modality correlation**: MODAL > PERF → epistemic reading;
   PERF > MODAL → counterfactual (metaphysical) reading. This follows
   from the **diversity condition** [45]: metaphysical modal bases
   require non-settledness, which the past cannot provide.

## Architecture

- Theory-layer primitives (`AT`, `atForward`) live in
  `Theories/Semantics/Tense/AT.lean`.
- Branching time, settledness, diversity live in
  `Theories/Semantics/Tense/BranchingTime.lean`.
- This file composes them into Condoravdi's specific operators and
  derives the paper's predictions.
-/

namespace Phenomena.Modality.Studies.Condoravdi2002

open Core.Time
open Core.Verbs (Dynamicity)
open Semantics.Tense.Aspect.Core
open Semantics.Tense.AT
open Semantics.Tense.BranchingTime

variable {W Time : Type*} [LinearOrder Time]

/-! ## Condoravdi's Operators -/

/-- PRES [20]: present tense instantiates a property at `now`.
    `λPλw[AT(now, w, P)]` — the temporal anchor is the utterance time. -/
def presC (sort : Dynamicity) (P : EventPred W Time) (now : Time)
    (w : W) : Prop :=
  at' sort P w (Interval.point now)

/-- PERF [21]: the perfect shifts evaluation to a prior time.
    `λPλwλt∃t'[t' ≺ t ∧ AT(t', w, P)]` -/
def perfC (sort : Dynamicity) (P : EventPred W Time) (w : W)
    (t : Time) : Prop :=
  ∃ t' : Time, t' < t ∧ at' sort P w (Interval.point t')

/-- MAY/MIGHT [22]: existential quantification over the modal base with
    forward temporal expansion.
    `λPλwλt∃w'[w' ∈ MB(w,t) ∧ AT([t,_), w', P)]` -/
def mayC (MB : W → Time → Set W) (sort : Dynamicity)
    (P : EventPred W Time) (w : W) (t : Time) : Prop :=
  ∃ w' ∈ MB w t, atForward sort P w' t

/-- WOLL [23]: universal quantification over the modal base with forward
    temporal expansion. The untensed modal underlying `will`.
    `λPλwλt∀w'[w' ∈ MB(w,t) → AT([t,_), w', P)]` -/
def wollC (MB : W → Time → Set W) (sort : Dynamicity)
    (P : EventPred W Time) (w : W) (t : Time) : Prop :=
  ∀ w' ∈ MB w t, atForward sort P w' t

@[simp] theorem presC_eq (sort : Dynamicity) (P : EventPred W Time)
    (now : Time) (w : W) :
    presC sort P now w = at' sort P w (Interval.point now) := rfl

@[simp] theorem perfC_eq (sort : Dynamicity) (P : EventPred W Time)
    (w : W) (t : Time) :
    perfC sort P w t =
      (∃ t' : Time, t' < t ∧ at' sort P w (Interval.point t')) := rfl

@[simp] theorem mayC_eq (MB : W → Time → Set W) (sort : Dynamicity)
    (P : EventPred W Time) (w : W) (t : Time) :
    mayC MB sort P w t = (∃ w' ∈ MB w t, atForward sort P w' t) := rfl

@[simp] theorem wollC_eq (MB : W → Time → Set W) (sort : Dynamicity)
    (P : EventPred W Time) (w : W) (t : Time) :
    wollC MB sort P w t = (∀ w' ∈ MB w t, atForward sort P w' t) := rfl

/-! ## Composed Readings -/

/-- "He might be here" [25]: PRES(MIGHT(stative P)).
    Present perspective, stative predicate: the state overlaps `[now,_)`,
    so it may extend into the past or future of utterance time. -/
def mightBeHere (MB : W → Time → Set W) (P : EventPred W Time)
    (now : Time) (w : W) : Prop :=
  mayC MB .stative P w now

/-- "He might run" [26]: PRES(MIGHT(eventive P)).
    Present perspective, eventive predicate: the event is contained
    in `[now,_)`, so it must occur in the future. -/
def mightRun (MB : W → Time → Set W) (P : EventPred W Time)
    (now : Time) (w : W) : Prop :=
  mayC MB .dynamic P w now

/-- "He may have won" — epistemic reading [27]:
    PRES(MAY(PERF(eventive P))). The modal scopes over the perfect.

    The relevant modal base is evaluated at `now` (present perspective).
    PERF back-shifts: ∃t'≺now such that the event is AT t'. -/
def mayHaveEpistemic (MB : W → Time → Set W) (P : EventPred W Time)
    (now : Time) (w : W) : Prop :=
  ∃ w' ∈ MB w now, perfC .dynamic P w' now

/-- "He might have won" — counterfactual reading [33]:
    PRES(PERF(MIGHT(eventive P))). The perfect scopes over the modal.

    PERF shifts perspective to past time t': ∃t'≺now such that at t',
    the modal base (evaluated at t') contains a world where the event
    occurs in `[t',_)`. -/
def mightHaveCF (MB : W → Time → Set W) (P : EventPred W Time)
    (now : Time) (w : W) : Prop :=
  ∃ t' : Time, t' < now ∧ mayC MB .dynamic P w t'

/-! ## Perspective × Orientation Table [9] -/

/-- Temporal perspective: the time at which the modal base is evaluated. -/
inductive Perspective where
  /-- Present: modal base evaluated at utterance time -/
  | present
  /-- Past: modal base evaluated at a prior time (via PERF > MODAL) -/
  | past
  deriving DecidableEq, Repr

/-- Temporal orientation: the direction of temporal reference for the
    property in the modal's scope. -/
inductive Orientation where
  /-- Future: property instantiated after the perspective time -/
  | future
  /-- Past: property instantiated before the perspective time -/
  | past
  deriving DecidableEq, Repr

/-- A classified modal temporal reading. -/
structure ModalReading where
  perspective : Perspective
  orientation : Orientation
  deriving DecidableEq, Repr

/-- Modals for the present: present perspective, future orientation.
    "He might win the game." -/
def modalsForPresent : ModalReading :=
  ⟨.present, .future⟩

/-- Modals for the past, epistemic reading: present perspective, past
    orientation. "He might have (already) won the game." -/
def modalsForPastEpistemic : ModalReading :=
  ⟨.present, .past⟩

/-- Modals for the past, counterfactual reading: past perspective, future
    orientation. "He might (still) have won the game." -/
def modalsForPastCF : ModalReading :=
  ⟨.past, .future⟩

/-- The attested readings are exactly these three. -/
def attestedReadings : List ModalReading :=
  [modalsForPresent, modalsForPastEpistemic, modalsForPastCF]

/-- Past perspective + past orientation is unattested: no modal has both
    a shifted-back perspective and a further-back-shifted orientation. -/
theorem no_past_past :
    (⟨.past, .past⟩ : ModalReading) ∉ attestedReadings := by decide

/-- Each attested reading is distinct. -/
theorem readings_distinct :
    attestedReadings.Nodup := by decide

/-! ## Bridge to Klein's PERF -/

/-- Condoravdi's `perfC` for eventive predicates entails Klein's
    `perfSimple`: if there is a prior time at which the event is
    instantiated (at a point), then the PTS-based perfect holds with a
    degenerate PTS `[t', t']` right-bounded at `t`. -/
theorem perfC_eventive_implies_perfSimple
    (P : EventPred W Time) (w : W) (t : Time)
    (h : perfC .dynamic P w t) : perfSimple P ⟨w, t⟩ := by
  obtain ⟨t', hlt, e, hP, hSub⟩ := h
  -- hSub : e.runtime.subinterval (Interval.point t')
  -- i.e. t' ≤ e.runtime.start ∧ e.runtime.finish ≤ t'
  -- Construct PTS = [t', t] with RB at t
  exact ⟨⟨t', t, le_of_lt hlt⟩, rfl, e,
    ⟨hSub.1, le_trans hSub.2 (le_of_lt hlt)⟩, hP⟩

/-! ## Scope–Modality Correlation -/

/-! The central empirical observation: the relative scope of MODAL and
    PERF correlates with the kind of modality expressed.

    - MODAL > PERF (epistemic reading [27]): the modal's perspective is
      present. The property it applies to is instantiated in the past
      (via PERF). Since past properties are settled, the diversity
      condition blocks a metaphysical modal base. The modal base must
      be epistemic.

    - PERF > MODAL (counterfactual reading [33]): the modal's perspective
      is a past time t' (set by PERF). The property it applies to is
      instantiated in the future of t'. Since future properties are not
      settled, the diversity condition is satisfiable. A metaphysical
      modal base is available.

    The theorem below captures the first direction: epistemic-only
    when the modal scopes over PERF. -/

/-- When the modal scopes over PERF (epistemic reading), the property
    under the modal is "there was a prior event of type P." If this
    property is settled in the common ground (as past properties always
    are), then a metaphysical modal base cannot satisfy diversity.

    This derives the restriction to epistemic modality for
    MODAL > PERF configurations. -/
theorem modal_over_perf_blocks_metaphysical
    (history : WorldHistory W Time)
    (MB : W → Time → Set W)
    (cg : Set W) (now : Time)
    (P : EventPred W Time)
    (hMB : ∀ w ∈ cg, ∀ w' ∈ MB w now, histEquiv history now w w')
    (hSettled : settled history cg now (λ w => perfC .dynamic P w now)) :
    ¬ diverse MB cg now (λ w => perfC .dynamic P w now) :=
  settled_not_diverse history MB cg now _ hMB hSettled

/-- @cite{condoravdi-2002} §4.2: when PERF > MODAL with a metaphysical
    modal base, the accessible worlds at past time `t'` are a superset
    of those at `now`. The modal at `t'` quantifies over worlds that
    have since diverged from the actual history — worlds outside the
    common ground's ≃_{now}-classes. This is the structural source of
    the counterfactual reading. -/
theorem counterfactual_widens_domain
    (history : WorldHistory W Time)
    (hBC : history.backwardsClosed) (w : W)
    {t' now : Time} (hle : t' ≤ now) :
    metaphysicalBase history w now ⊆ metaphysicalBase history w t' :=
  metaphysicalBase_antitone hBC w hle

/-! ## Adverb Compatibility

@cite{condoravdi-2002} [1]–[2]: frame adverbials restrict the temporal
reference of the sentence. The compatibility patterns are **derived from**
the AT relation, not stipulated: the sort-dependent temporal constraint
(⊆ for events, ∘ for states) determines which temporal regions the modal
can reach, and compatibility holds when the adverb selects a reachable
region. -/

/-- The temporal region a frame adverb selects. -/
inductive TemporalRegion where
  | past    -- before the perspective time (e.g. "yesterday")
  | present -- at the perspective time (e.g. "now")
  | future  -- after the perspective time (e.g. "tomorrow")
  deriving DecidableEq, Repr

/-- Frame adverb temporal restriction. -/
inductive FrameAdverb where
  | yesterday
  | now_
  | tomorrow
  deriving DecidableEq, Repr

/-- The temporal region selected by a frame adverb. -/
def FrameAdverb.region : FrameAdverb → TemporalRegion
  | .yesterday => .past
  | .now_ => .present
  | .tomorrow => .future

/-- The temporal reference direction imposed by a modal's orientation and
    the predicate sort, derived from the AT relation:

    - `atEventForward` requires `now ≤ e.start` → event in the future.
    - `atStateForward` requires `now ≤ e.finish` → state extends through
      present or into future.
    - `perfC` requires `t' < now` → prior instantiation. -/
inductive ReferenceDirection where
  /-- Eventive + forward: `atEventForward` requires `t ≤ e.start`, so
      the event is located strictly after the perspective time. -/
  | futureOnly
  /-- Stative + forward: `atStateForward` requires `t ≤ e.finish`, so
      the state persists through or past the perspective time. -/
  | presentOrFuture
  /-- Via PERF: `perfC` requires `t' < t`, so the property is
      instantiated before the perspective time. -/
  | pastOnly
  deriving DecidableEq, Repr

/-- Derive the reference direction from a modal orientation and predicate
    sort. This is the factored core of the compatibility relation. -/
def referenceDirection : Orientation → Dynamicity → ReferenceDirection
  | .future, .dynamic => .futureOnly
  | .future, .stative => .presentOrFuture
  | .past, _ => .pastOnly

/-- Whether a reference direction can reach a temporal region.
    Follows from the AT relation's temporal constraints:
    - `futureOnly` reaches only future (from `atEventForward`)
    - `presentOrFuture` reaches present and future (from `atStateForward`)
    - `pastOnly` reaches only past (from `perfC`) -/
def ReferenceDirection.reaches : ReferenceDirection → TemporalRegion → Bool
  | .futureOnly, .future => true
  | .presentOrFuture, .present => true
  | .presentOrFuture, .future => true
  | .pastOnly, .past => true
  | _, _ => false

/-- Compatibility of a frame adverb with a modal reading at a given sort:
    the adverb's temporal region must be reachable by the reference
    direction derived from the AT relation. -/
def compatible (adv : FrameAdverb) (reading : ModalReading)
    (sort : Dynamicity) : Bool :=
  (referenceDirection reading.orientation sort).reaches adv.region

-- ── Eventive modals for the present ──

/-- [1a]: "He may get sick tomorrow" — eventive, future orientation. -/
theorem tomorrow_eventive_present_compat :
    compatible .tomorrow modalsForPresent .dynamic = true := by decide

/-- [1a]: "*He may get sick yesterday" — eventive, future orientation. -/
theorem yesterday_eventive_present_incompat :
    compatible .yesterday modalsForPresent .dynamic = false := by decide

/-- [1a]: "??He may get sick now" — eventive, future orientation.
    `atEventForward` requires `now ≤ e.start`, so the event must start
    at or after now; "now" as a point leaves no room for an event. -/
theorem now_eventive_present_incompat :
    compatible .now_ modalsForPresent .dynamic = false := by decide

-- ── Stative modals for the present ──

/-- [1c]: "He may be sick now" — stative, future orientation.
    `atStateForward` requires `now ≤ e.finish`, which is satisfied by
    a state extending through the present. -/
theorem now_stative_present_compat :
    compatible .now_ modalsForPresent .stative = true := by decide

/-- [1c]: "He may be sick tomorrow" — stative, future orientation. -/
theorem tomorrow_stative_present_compat :
    compatible .tomorrow modalsForPresent .stative = true := by decide

/-- [1c]: "*He may be sick yesterday" — stative, future orientation. -/
theorem yesterday_stative_present_incompat :
    compatible .yesterday modalsForPresent .stative = false := by decide

-- ── Modals for the past (epistemic) ──

/-- [2a]: "He may have gotten sick yesterday" — past orientation. -/
theorem yesterday_past_epistemic_compat :
    compatible .yesterday modalsForPastEpistemic .dynamic = true := by
  decide

/-- [2a]: "*He may have gotten sick tomorrow" — past orientation. -/
theorem tomorrow_past_epistemic_incompat :
    compatible .tomorrow modalsForPastEpistemic .dynamic = false := by
  decide

end Phenomena.Modality.Studies.Condoravdi2002
