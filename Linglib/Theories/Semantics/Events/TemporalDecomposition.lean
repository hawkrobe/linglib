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

end Semantics.Events
