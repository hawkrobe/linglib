import Linglib.Theories.Semantics.Events.Basic
import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect

/-!
# Temporal Decomposition of Events

Bridges the gap between `EventStructure.Template` (predicate-role decomposition,
no temporal information) and `ViewpointAspect` (temporal operators on opaque
predicates, no subevent structure).

Accomplishments and achievements have internal temporal structure: an activity
phase and a result phase with ordering constraints. States and activities are
temporally simple. This module makes that structure explicit via
`TemporalDecomposition`, enabling the perfect polysemy analysis in
`PerfectPolysemy.lean` (Kiparsky 2002).

## Key Definitions

- `SubeventPhases`: activity trace + result trace with ordering constraint
- `TemporalDecomposition`: `.simple` (single runtime) or `.complex` (phased)
- `hasComplexDecomposition`: telic classes have complex decomposition
- `DecomposedEv`: event enriched with decomposition
- `phasePred`: converts an interval (event phase) into an `EventPred` for
  ViewpointAspect operators
- `MoensSteedmanClass`: five-way event classification (Moens & Steedman 1988)
- `Nucleus`: tripartite event structure (prep process → culmination → cons state)
- `WhenTarget`: what *when* accesses in each event type

## ViewpointAspect Bridge (§ 6–7)

`phasePred` converts temporal phases into `EventPred Unit Time`, making them
consumable by IMPF/PRFV/PERF. Key results:

- `impf_phasePred` / `prfv_phasePred`: reduce operator applications to
  interval containment
- `progressive_before_result`: the imperfective paradox — IMPF on the
  activity phase can hold at times entirely before the result
- `perfective_full_entails_result`: PRFV on the full event entails the
  result trace is within the reference time
- `impf_activity_prfv_full_incompatible`: progressive and perfective are
  mutually exclusive at the same reference time

## References

- Moens, M. & Steedman, M. (1988). Temporal ontology and temporal reference.
- Kiparsky, P. (2002). Event structure and the perfect.
- Rappaport Hovav, M. & Levin, B. (1998). Building verb meanings.
- Pustejovsky, J. (1991). The syntax of event structure.
-/

namespace Semantics.Events

open Core.Time
open Semantics.Lexical.Verb.Aspect

-- ════════════════════════════════════════════════════
-- § 1. Subevent Phases
-- ════════════════════════════════════════════════════

/-- The two temporal phases of a complex event (accomplishment/achievement):
    an activity trace (the process) and a result trace (the outcome state).
    The activity phase must precede or meet the result phase. -/
structure SubeventPhases (Time : Type*) [LinearOrder Time] where
  /-- Temporal extent of the activity/process phase -/
  activityTrace : Interval Time
  /-- Temporal extent of the result state phase -/
  resultTrace : Interval Time
  /-- Activity precedes or meets result: activity ends ≤ result starts -/
  activity_precedes_result : activityTrace.finish ≤ resultTrace.start

-- ════════════════════════════════════════════════════
-- § 2. Temporal Decomposition
-- ════════════════════════════════════════════════════

/-- Temporal decomposition of an event: either simple (single runtime) or
    complex (runtime with internal activity + result phases).
    - States and activities are `.simple`: one homogeneous interval.
    - Accomplishments and achievements are `.complex`: the overall runtime
      decomposes into an activity phase and a result phase. -/
inductive TemporalDecomposition (Time : Type*) [LinearOrder Time] where
  /-- Simple event: a single runtime interval with no internal structure. -/
  | simple (runtime : Interval Time)
  /-- Complex event: overall runtime with activity and result subphases.
      Both subphases are contained within the overall runtime. -/
  | complex
    (runtime : Interval Time)
    (phases : SubeventPhases Time)
    (activity_in_runtime : phases.activityTrace.subinterval runtime)
    (result_in_runtime : phases.resultTrace.subinterval runtime)

namespace TemporalDecomposition

variable {Time : Type*} [LinearOrder Time]

/-- Extract the overall runtime from any decomposition. -/
def runtime : TemporalDecomposition Time → Interval Time
  | .simple r => r
  | .complex r _ _ _ => r

/-- Extract the activity phase (only available for complex events). -/
def activityPhase : TemporalDecomposition Time → Option (Interval Time)
  | .simple _ => none
  | .complex _ phases _ _ => some phases.activityTrace

/-- Extract the result phase (only available for complex events). -/
def resultPhase : TemporalDecomposition Time → Option (Interval Time)
  | .simple _ => none
  | .complex _ phases _ _ => some phases.resultTrace

/-- Is this a complex (phased) decomposition? -/
def isComplex : TemporalDecomposition Time → Bool
  | .simple _ => false
  | .complex _ _ _ _ => true

end TemporalDecomposition

-- ════════════════════════════════════════════════════
-- § 3. VendlerClass ↔ Complexity Bridge
-- ════════════════════════════════════════════════════

/-- Telic Vendler classes (accomplishment, achievement) have complex temporal
    structure with distinguishable activity and result phases. Atelic classes
    (state, activity) are temporally simple. -/
def hasComplexDecomposition : VendlerClass → Bool
  | .accomplishment => true
  | .achievement => true
  | .state => false
  | .activity => false

/-- Complex decomposition ↔ telicity. -/
theorem hasComplexDecomposition_iff_telic (c : VendlerClass) :
    hasComplexDecomposition c = (c.telicity == .telic) := by
  cases c <;> rfl

-- ════════════════════════════════════════════════════
-- § 4. Ev with Decomposition
-- ════════════════════════════════════════════════════

/-- An event enriched with temporal decomposition information.
    Extends `Ev` (which has runtime + sort) with subevent phase structure. -/
structure DecomposedEv (Time : Type*) [LinearOrder Time] where
  /-- The underlying event -/
  event : Ev Time
  /-- Temporal decomposition of the event -/
  decomposition : TemporalDecomposition Time
  /-- The decomposition's runtime matches the event's runtime -/
  runtime_consistent : decomposition.runtime = event.runtime

/-- Attach a simple decomposition to an event (for states/activities). -/
def Ev.withSimpleDecomposition {Time : Type*} [LinearOrder Time]
    (e : Ev Time) : DecomposedEv Time where
  event := e
  decomposition := .simple e.runtime
  runtime_consistent := rfl

/-- Attach a complex decomposition to an event (for accomplishments/achievements). -/
def Ev.withComplexDecomposition {Time : Type*} [LinearOrder Time]
    (e : Ev Time) (phases : SubeventPhases Time)
    (h_act : phases.activityTrace.subinterval e.runtime)
    (h_res : phases.resultTrace.subinterval e.runtime) : DecomposedEv Time where
  event := e
  decomposition := .complex e.runtime phases h_act h_res
  runtime_consistent := rfl

-- ════════════════════════════════════════════════════
-- § 5. Structural Theorems
-- ════════════════════════════════════════════════════

/-- Activity precedes result in any SubeventPhases (direct accessor). -/
theorem SubeventPhases.ordering {Time : Type*} [LinearOrder Time]
    (p : SubeventPhases Time) : p.activityTrace.finish ≤ p.resultTrace.start :=
  p.activity_precedes_result

/-- Both subevent phases are contained in the overall runtime of a complex
    decomposition (by construction). -/
theorem complex_phases_in_runtime {Time : Type*} [LinearOrder Time]
    (rt : Interval Time) (phases : SubeventPhases Time)
    (h_act : phases.activityTrace.subinterval rt)
    (h_res : phases.resultTrace.subinterval rt) :
    phases.activityTrace.subinterval rt ∧
    phases.resultTrace.subinterval rt :=
  ⟨h_act, h_res⟩

/-- A simple decomposition has no result phase. -/
theorem simple_no_result {Time : Type*} [LinearOrder Time]
    (r : Interval Time) :
    (TemporalDecomposition.simple r).resultPhase = none := rfl

/-- A simple decomposition has no activity phase. -/
theorem simple_no_activity {Time : Type*} [LinearOrder Time]
    (r : Interval Time) :
    (TemporalDecomposition.simple r).activityPhase = none := rfl

-- ════════════════════════════════════════════════════
-- § 6. Phase Event Predicates
-- ════════════════════════════════════════════════════

open Semantics.Lexical.Verb.ViewpointAspect

/-- Event predicate localized to an interval: holds of eventualities whose
    runtime equals the given interval. Converts temporal phases of a
    `DecomposedEv` into predicates consumable by ViewpointAspect operators
    (IMPF, PRFV, PERF).

    The world parameter is fixed to `Unit` since temporal decomposition
    is world-independent (following the same convention as
    `Giannakidou.lean`). -/
def phasePred {Time : Type*} [LinearOrder Time]
    (phase : Interval Time) : EventPred Unit Time :=
  λ _ ev => ev.runtime = phase

/-- IMPF applied to a phase predicate reduces to the reference time being
    properly inside that phase interval. -/
theorem impf_phasePred {Time : Type*} [LinearOrder Time]
    (phase t : Interval Time) :
    IMPF (phasePred phase) () t ↔ t.properSubinterval phase := by
  simp only [IMPF, phasePred, Eventuality.τ]
  constructor
  · rintro ⟨e, hSub, rfl⟩; exact hSub
  · intro h; exact ⟨⟨phase⟩, h, rfl⟩

/-- PRFV applied to a phase predicate reduces to the phase interval being
    contained in the reference time. -/
theorem prfv_phasePred {Time : Type*} [LinearOrder Time]
    (phase t : Interval Time) :
    PRFV (phasePred phase) () t ↔ phase.subinterval t := by
  simp only [PRFV, phasePred, Eventuality.τ]
  constructor
  · rintro ⟨e, hSub, rfl⟩; exact hSub
  · intro h; exact ⟨⟨phase⟩, h, rfl⟩

-- ════════════════════════════════════════════════════
-- § 7. ViewpointAspect ↔ Decomposition Bridge
-- ════════════════════════════════════════════════════

/-- The imperfective paradox via temporal decomposition: IMPF on the
    activity phase can hold at reference times entirely before the result
    phase. "Was building a house" doesn't entail a house was built.

    Counterexample: activity = [0, 10], result = [15, 20], ref = [3, 7].
    The reference [3, 7] is properly inside the activity [0, 10], but
    entirely before the result [15, 20]. -/
theorem progressive_before_result :
    ∃ (phases : SubeventPhases ℤ) (t : Interval ℤ),
      IMPF (phasePred phases.activityTrace) () t ∧
      t.isBefore phases.resultTrace := by
  refine ⟨⟨⟨0, 10, by omega⟩, ⟨15, 20, by omega⟩, by dsimp; omega⟩,
         ⟨3, 7, by omega⟩, ?_, ?_⟩
  · rw [impf_phasePred]
    refine ⟨⟨?_, ?_⟩, Or.inl ?_⟩ <;> dsimp [Interval.subinterval] <;> omega
  · dsimp [Interval.isBefore]; omega

/-- PRFV on the full event entails the result trace is within the reference
    time. "Built a house" entails the building was completed: the result
    phase is contained in any reference time that contains the whole event.

    Proof: result ⊆ runtime (by `h_res`) and runtime ⊆ ref (by PRFV),
    so result ⊆ ref by transitivity. -/
theorem perfective_full_entails_result {Time : Type*} [LinearOrder Time]
    (rt : Interval Time) (phases : SubeventPhases Time)
    (h_res : phases.resultTrace.subinterval rt)
    (t : Interval Time)
    (h_prfv : PRFV (phasePred rt) () t) :
    phases.resultTrace.subinterval t := by
  rw [prfv_phasePred] at h_prfv
  exact ⟨le_trans h_prfv.1 h_res.1, le_trans h_res.2 h_prfv.2⟩

/-- PRFV on the full event entails the activity trace is within the
    reference time. The process phase is also covered. -/
theorem perfective_full_entails_activity {Time : Type*} [LinearOrder Time]
    (rt : Interval Time) (phases : SubeventPhases Time)
    (h_act : phases.activityTrace.subinterval rt)
    (t : Interval Time)
    (h_prfv : PRFV (phasePred rt) () t) :
    phases.activityTrace.subinterval t := by
  rw [prfv_phasePred] at h_prfv
  exact ⟨le_trans h_prfv.1 h_act.1, le_trans h_act.2 h_prfv.2⟩

/-- For complex events, PRFV on the full event entails both subevent phases
    are within the reference time. This is the compositional account of why
    perfective aspect entails completion for accomplishments. -/
theorem perfective_full_covers_phases {Time : Type*} [LinearOrder Time]
    (rt : Interval Time) (phases : SubeventPhases Time)
    (h_act : phases.activityTrace.subinterval rt)
    (h_res : phases.resultTrace.subinterval rt)
    (t : Interval Time)
    (h_prfv : PRFV (phasePred rt) () t) :
    phases.activityTrace.subinterval t ∧ phases.resultTrace.subinterval t :=
  ⟨perfective_full_entails_activity rt phases h_act t h_prfv,
   perfective_full_entails_result rt phases h_res t h_prfv⟩

/-- IMPF on the activity phase is incompatible with PRFV on the full event
    at the same reference time: the progressive and perfective can't
    simultaneously hold for the same temporal window.

    Proof: IMPF requires ref ⊂ activity (proper subset). PRFV requires
    runtime ⊆ ref. Since activity ⊆ runtime (by `h_act`), we get
    activity ⊆ ref. Combined with ref ⊆ activity (from IMPF), this forces
    ref = activity, contradicting the strict inequality in properSubinterval. -/
theorem impf_activity_prfv_full_incompatible {Time : Type*} [LinearOrder Time]
    (rt : Interval Time) (phases : SubeventPhases Time)
    (h_act : phases.activityTrace.subinterval rt)
    (t : Interval Time) :
    IMPF (phasePred phases.activityTrace) () t →
    ¬ PRFV (phasePred rt) () t := by
  rw [impf_phasePred, prfv_phasePred]
  intro ⟨⟨h1, h2⟩, h_strict⟩ ⟨h3, h4⟩
  -- h1 : activity.start ≤ t.start, h2 : t.finish ≤ activity.finish
  -- h3 : t.start ≤ rt.start, h4 : rt.finish ≤ t.finish
  -- h_act : rt.start ≤ activity.start ∧ activity.finish ≤ rt.finish
  -- Chain: activity.start ≤ t.start ≤ rt.start ≤ activity.start → equal
  -- Chain: t.finish ≤ activity.finish ≤ rt.finish ≤ t.finish → equal
  have heq_s := le_antisymm h1 (le_trans h3 h_act.1)
  have heq_f := le_antisymm h2 (le_trans h_act.2 h4)
  cases h_strict with
  | inl h => exact absurd heq_s (ne_of_lt h)
  | inr h => exact absurd heq_f (ne_of_lt h)

-- ════════════════════════════════════════════════════
-- § 8. Moens & Steedman (1988) Event Types
-- ════════════════════════════════════════════════════

/-- Moens & Steedman's (1988) aspectual profile. Extends Vendler's
    three-feature `AspectualProfile` with ±consequent state, so the
    Vendler classification is inherited rather than stipulated.
    @cite{moens-steedman-1988} -/
structure MoensSteedmanProfile extends AspectualProfile where
  /-- Whether the event has a persistent result after culmination -/
  hasConsequentState : Bool
  deriving DecidableEq, Repr, BEq

/-- Moens & Steedman's (1988) five-way event classification.
    Refines Vendler by splitting `achievement` along ±consequent state:

    | Class             | Atomic? | +ConsState? | Vendler        |
    |-------------------|---------|-------------|----------------|
    | state             | no      | —           | state          |
    | process           | no      | no          | activity       |
    | culminatedProcess | no      | yes         | accomplishment |
    | culmination       | yes     | yes         | achievement    |
    | point             | yes     | no           | (none)         |

    @cite{moens-steedman-1988} -/
inductive MoensSteedmanClass where
  | state             -- know, love
  | process           -- run, swim
  | culminatedProcess -- build a house, write a letter
  | culmination       -- arrive, die, recognize
  | point             -- hiccup, flash, tap
  deriving DecidableEq, Repr, BEq

namespace MoensSteedmanClass

/-- Canonical profile for each M&S event type. The `VendlerClass` is
    inherited from `AspectualProfile` via `extends` — accessible as
    `c.toProfile.toVendlerClass` without a separate mapping function. -/
def toProfile : MoensSteedmanClass → MoensSteedmanProfile
  | .state => { stateProfile with hasConsequentState := false }
  | .process => { activityProfile with hasConsequentState := false }
  | .culminatedProcess => { accomplishmentProfile with hasConsequentState := true }
  | .culmination => { achievementProfile with hasConsequentState := true }
  | .point => { achievementProfile with hasConsequentState := false }

/-- Whether the event is atomic (instantaneous). -/
def isAtomic : MoensSteedmanClass → Bool
  | .culmination | .point => true
  | .state | .process | .culminatedProcess => false

/-- Points and culminations share a Vendler class (achievement) but differ
    in ±consequent state — exactly the conflation Moens & Steedman identify. -/
theorem point_culmination_vendler_collapse :
    point.toProfile.toVendlerClass = culmination.toProfile.toVendlerClass ∧
    point.toProfile.hasConsequentState ≠ culmination.toProfile.hasConsequentState :=
  ⟨rfl, by decide⟩

/-- Points are telic (achievements) but lack consequent states — the reason
    Vendler's classification is too coarse for the perfect. -/
theorem point_telic_without_consState :
    point.toProfile.telicity = .telic ∧ point.toProfile.hasConsequentState = false :=
  ⟨rfl, rfl⟩

/-- Atomicity matches Vendler's punctuality for dynamic classes. -/
theorem isAtomic_iff_punctual (c : MoensSteedmanClass) (h : c ≠ .state) :
    c.isAtomic = (c.toProfile.duration == .punctual) := by
  cases c <;> first | exact absurd rfl h | rfl

end MoensSteedmanClass

-- ════════════════════════════════════════════════════
-- § 9. Unified When-Clause Semantics (M&S 1988)
-- ════════════════════════════════════════════════════

/-- What *when* accesses in each event type. M&S's key claim: *when* has
    a single meaning (locate the main clause at the culmination), with
    apparent ambiguity arising from different nucleus structures.
    @cite{moens-steedman-1988} -/
inductive WhenTarget where
  | directCulmination   -- culmination/point: event IS the culmination
  | completionCoercion  -- culminated process: strip prep, access culmination
  | inceptionCoercion   -- process: INCHOAT extracts onset as surrogate
  | homogeneousOverlap  -- state: any subinterval works
  deriving DecidableEq, Repr, BEq

/-- M&S's unified *when* semantics: one meaning, four behaviors derived
    from event type. -/
def MoensSteedmanClass.whenTarget : MoensSteedmanClass → WhenTarget
  | .culmination | .point => .directCulmination
  | .culminatedProcess => .completionCoercion
  | .process => .inceptionCoercion
  | .state => .homogeneousOverlap

/-- Coercion is needed iff the event type is process or culminated process. -/
theorem MoensSteedmanClass.when_needs_coercion_iff (c : MoensSteedmanClass) :
    (c.whenTarget = .completionCoercion ∨ c.whenTarget = .inceptionCoercion) ↔
    (c = .culminatedProcess ∨ c = .process) := by
  cases c <;> simp [MoensSteedmanClass.whenTarget]

-- ════════════════════════════════════════════════════
-- § 10. The Nucleus (Tripartite Event Structure)
-- ════════════════════════════════════════════════════

/-- The Moens & Steedman (1988) nucleus: tripartite event structure for
    events with a culmination point. Makes the culmination explicit —
    it is implicit in `SubeventPhases` as the boundary between
    activityTrace and resultTrace.

    ```
    SubeventPhases:  |---activity---|    |---result---|
    Nucleus:         |---prep-------|•c  |---cons-----|
                                     ↑
                             explicit culmination
    ```
    @cite{moens-steedman-1988} -/
structure Nucleus (Time : Type*) [LinearOrder Time] where
  /-- Preparatory process leading to culmination -/
  prepProcess : Option (Interval Time)
  /-- The culmination point: instantaneous transition -/
  culmination : Time
  /-- Consequent state persisting after culmination -/
  consState : Option (Interval Time)
  /-- Prep process ends at or before culmination -/
  prep_le_culm : ∀ i, prepProcess = some i → i.finish ≤ culmination
  /-- Consequent state starts at or after culmination -/
  culm_le_cons : ∀ i, consState = some i → culmination ≤ i.start

namespace Nucleus

variable {Time : Type*} [LinearOrder Time]

/-- The M&S event type determined by which components are present. -/
def eventType (n : Nucleus Time) : MoensSteedmanClass :=
  match n.prepProcess, n.consState with
  | some _, some _ => .culminatedProcess
  | none,   some _ => .culmination
  | _,      none   => .point

/-- A full nucleus (both prep and cons present) yields SubeventPhases.
    The ordering proof follows from transitivity through the culmination. -/
def toSubeventPhases (n : Nucleus Time)
    (prep cons : Interval Time)
    (h_prep : n.prepProcess = some prep)
    (h_cons : n.consState = some cons) :
    SubeventPhases Time where
  activityTrace := prep
  resultTrace := cons
  activity_precedes_result :=
    le_trans (n.prep_le_culm prep h_prep) (n.culm_le_cons cons h_cons)

/-- A full nucleus has event type culminatedProcess. -/
theorem full_is_culminatedProcess (n : Nucleus Time)
    {p c : Interval Time}
    (hp : n.prepProcess = some p) (hc : n.consState = some c) :
    n.eventType = .culminatedProcess := by
  simp [eventType, hp, hc]

/-- A nucleus with consequent state has M&S's consequent state feature. -/
theorem hasConsState_of_consState (n : Nucleus Time)
    {c : Interval Time} (hc : n.consState = some c) :
    n.eventType.toProfile.hasConsequentState = true := by
  simp only [eventType]
  split <;> simp_all [MoensSteedmanClass.toProfile]

end Nucleus

end Semantics.Events
