import Linglib.Theories.EventSemantics.Basic
import Linglib.Theories.TruthConditional.Verb.ViewpointAspect

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

## References

- Kiparsky, P. (2002). Event structure and the perfect.
- Rappaport Hovav, M. & Levin, B. (1998). Building verb meanings.
- Pustejovsky, J. (1991). The syntax of event structure.
-/

namespace EventSemantics

open Core.Time
open TruthConditional.Verb.Aspect

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

end EventSemantics
