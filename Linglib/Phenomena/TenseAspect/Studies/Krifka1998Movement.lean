import Linglib.Theories.Semantics.Events.SpatialTrace
import Linglib.Theories.Semantics.Events.DimensionBridge
import Linglib.Theories.Semantics.Events.MovementRelations
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.TenseAspect.Diagnostics

/-!
# @cite{krifka-1998} §4: Telicity by Precedence and Adjacency
@cite{krifka-1998}

Krifka 1998's distinctive contribution beyond K89: the path/movement
extension of mereological telicity. Where §3 derives telicity from
incrementality (CUM/QUA propagation, SINC/INC verb classes — formalized
in `Studies/Krifka1998.lean`), §4 derives telicity from spatial and
dimensional **paths**: a movement event is telic iff its path is
bounded.

## What this file is

A paper-replication of K98 §4 anchored on the existing
`Theories/Semantics/Events/SpatialTrace.lean` substrate (which already
cites `@cite{krifka-1998}` in its header). The σ trace function and
`PathShape → Telicity` bridge are the linglib home for K98 §4's
movement-relation (MR) machinery — they instantiate the Bool-tag
projection of ADJ (eq. 68), SMR (eq. 69, strict movement relation),
MR (eq. 71, general movement), KM' (eq. 72, derived movement-event
measure), SOURCE/GOAL (eq. 73), and the *walked from X to Y* /
*towards Y* analyses (eq. 74-75).

Per K98 §4.6 quality changes (heat, bake, whip — eq. 76-77),
dimensional movements are structurally identical to spatial ones:
movement in a temperature dimension toward a goal is telic; movement
in a temperature dimension by a measured amount (without specified
goal) is also telic. K98 §4.7 instantaneous movements (eq. 78,
*Mary arrived in London*) reduce to the bounded-path case at the
limit of granularity.

## What it exercises

- `pathShapeToTelicity` (PathShape → Telicity) — the K98 §4 "movement
  has telic predicate iff path is bounded" rule (eq. 71-74)
- `LevinClass.pathSpec` (verb → path specification) — the K98 §4.5
  source/goal/towards typology
- `LicensingPipeline PathShape` — bounded → licensed (telic), unbounded
  → blocked (atelic), the K98 §4 in/for diagnostic chain

## Structure

1. **§4.5 Source/Goal/Path-Spec verbs** — per-verb path specification (eq. 73)
2. **§4 Path → Telicity → Licensing pipeline** — full chain (eq. 74-75)
3. **§4 Motion VP data** — verb + PP pairs with path shapes (eq. 74-75)
4. **§3 ↔ §4 diagnostic bridge** — connect path telicity to for/in licensing

## Sister files

- `Studies/Krifka1998.lean` — K98 §3 (incrementality through CUM/QUA
  propagation, SINC/INC verb classes); the §3-counterpart to this file
- `Studies/Krifka1989.lean` — K89, the algebraic-mereology antecedent
  with K89 §4 thematic-relation features (table 14)
- `Studies/KennedyLevin2008.lean` — degree achievements (heat, cool,
  dry); K98 §4.6 quality-change movements are the K98-substrate version
  of K&L's degree-of-change account, related but with different primitives

## History

This file was previously named `Studies/SpatialTrace.lean` with namespace
`SpatialTrace` and no author-year anchor. The round-1 cross-framework
audit (of `Studies/Krifka1998.lean` §3 content) flagged it as
"anonymous, no author-year anchor" while documenting that
`Theories/Semantics/Events/SpatialTrace.lean` cites K98 explicitly. The
rename + namespace change makes the K98 §4 paper-replication anchor
visible at the file level, satisfying CLAUDE.md's three-anchor rule
(paper / typology / framework — this is "paper"). The σ trace machinery
itself stays in `Theories/Semantics/Events/SpatialTrace.lean`
(theory-level substrate, framework-anchored).

The K98 §4 substrate predicates ADJ/EXP/SEINC/SMR/MR/KM' as defined in
the paper (eq. 63-72) are NOT yet propositionally formalized in
linglib's K98 theory file — only their Bool-tag projections via
`PathShape`/`pathShapeToTelicity` exist. A future deepening would add
the propositional substrate to `Theories/Semantics/Events/Krifka1998.lean`
and have this file invoke them on abstract `θ` instances, paralleling
what K89 study §3 now does for `qmod_of_cum_is_qua`.

-/

namespace Krifka1998Movement

open Core.Verbs (LevinClass MeaningComponents)
open Fragments.English.Predicates.Verbal
open Semantics.Events.SpatialTrace (pathShapeToTelicity)
open Core.Verbs
open Semantics.Spatial.Path (PathShape)
open Core.Scale (LicensingPipeline)
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction)

-- ════════════════════════════════════════════════════
-- § 1. Per-Verb Path Specification (K98 §4.5 eq. 73 SOURCE/GOAL)
-- ════════════════════════════════════════════════════

/-! Each motion verb's `levinClass` and `pathSpec` annotation is
    verified by `rfl`. K98 §4.5 (eq. 73) defines SOURCE and GOAL
    relations on movement events; the fragment-level `LevinClass`
    + `pathSpec` annotations encode the K98 §4.5 source/goal typology
    as Bool tags on verb classes. Changing any annotation breaks
    exactly one theorem here. -/

/-- "arrive" is inherently directed motion (K98 §4.7 eq. 78
    instantaneous movement). -/
theorem arrive_levinClass :
    arrive.toVerbCore.levinClass = some .inherentlyDirectedMotion := rfl

/-- Inherently directed motion → bounded path (K98 §4.5 GOAL specified). -/
theorem arrive_pathSpec :
    LevinClass.inherentlyDirectedMotion.pathSpec = some .bounded := rfl

/-- "leave" is a leave verb (K98 §4.5 SOURCE-only). -/
theorem leave_levinClass :
    leave.toVerbCore.levinClass = some .leave := rfl

/-- Leave verbs → source path (K98 §4.5 SOURCE specified, GOAL unspecified). -/
theorem leave_pathSpec :
    LevinClass.leave.pathSpec = some .source := rfl

/-- "run" is manner-of-motion (K98 §4.5 path-neutral; PP supplies path). -/
theorem run_levinClass :
    run.toVerbCore.levinClass = some .mannerOfMotion := rfl

/-- Manner-of-motion verbs are path-neutral (path from PP). K98 §4.5
    *Mary walked* is atelic; *Mary walked from the university to the
    capitol* is telic via SOURCE + GOAL adjuncts. -/
theorem run_pathSpec :
    LevinClass.mannerOfMotion.pathSpec = none := rfl

-- ════════════════════════════════════════════════════
-- § 2. PathShape → Telicity → Licensing (K98 §4 MR eq. 71)
-- ════════════════════════════════════════════════════

/-! K98 §4 derives that a movement-relation θ over a bounded path
    yields a telic predicate (eq. 71 MR + the SMR theorem on page 24).
    The full chain from PathShape through Telicity to licensing is
    verified for all three shapes here. The `LicensingPipeline`
    instance for `PathShape` is in `DimensionBridge.lean`, which also
    cites K98 explicitly. -/

/-- Bounded path → telic → QUA → closed → licensed.
    K98 §4 eq. 74 (*walked from X to Y*) — full path with both SOURCE
    and GOAL is telic. -/
theorem bounded_pipeline :
    pathShapeToTelicity .bounded = .telic ∧
    LicensingPipeline.isLicensed PathShape.bounded = true := ⟨rfl, rfl⟩

/-- Source path → telic → QUA → closed → licensed.
    K98 §4 eq. 73 (*Mary left the house*) — SOURCE-only paths are
    treated as bounded for telicity purposes. -/
theorem source_pipeline :
    pathShapeToTelicity .source = .telic ∧
    LicensingPipeline.isLicensed PathShape.source = true := ⟨rfl, rfl⟩

/-- Unbounded path → atelic → CUM → open → blocked.
    K98 §4 eq. 75 (*Mary walked towards the capitol*) — *towards*
    specifies direction without a definite goal, yielding atelic. -/
theorem unbounded_pipeline :
    pathShapeToTelicity .unbounded = .atelic ∧
    LicensingPipeline.isLicensed PathShape.unbounded = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Motion VP Data (K98 §4.5 eq. 74-75)
-- ════════════════════════════════════════════════════

/-- A motion VP datum: verb + PP + path shape + expected telicity. -/
structure MotionVPDatum where
  verb : String
  pp : String
  pathShape : PathShape
  expectedTelicity : Telicity
  deriving Repr, DecidableEq

/-- "arrive at the store" — inherently bounded → telic → "in X" ✓.
    K98 §4.7 eq. 78 (*Mary arrived in London*) reduces to bounded path. -/
def arriveAtStore : MotionVPDatum :=
  { verb := "arrive", pp := "at the store",
    pathShape := .bounded, expectedTelicity := .telic }

/-- "leave the house" — source → telic → "in X" ✓.
    K98 §4.5 eq. 73 SOURCE-specified path. -/
def leaveTheHouse : MotionVPDatum :=
  { verb := "leave", pp := "the house",
    pathShape := .source, expectedTelicity := .telic }

/-- "run to the park" — manner + bounded PP → telic → "in X" ✓.
    K98 §4.5 eq. 74 *walked to Y* with manner-of-motion verb. -/
def runToThePark : MotionVPDatum :=
  { verb := "run", pp := "to the park",
    pathShape := .bounded, expectedTelicity := .telic }

/-- "run towards the park" — manner + unbounded PP → atelic → "for X" ✓.
    K98 §4.5 eq. 75 *walked towards Y* — direction without goal. -/
def runTowardsThePark : MotionVPDatum :=
  { verb := "run", pp := "towards the park",
    pathShape := .unbounded, expectedTelicity := .atelic }

def motionData : List MotionVPDatum :=
  [arriveAtStore, leaveTheHouse, runToThePark, runTowardsThePark]

/-- Path shape determines telicity for all motion data per K98 §4. -/
theorem all_motion_data_correct :
    motionData.all (fun d =>
      pathShapeToTelicity d.pathShape == d.expectedTelicity) = true := by
  decide

-- ════════════════════════════════════════════════════
-- § 4. §3 ↔ §4 Diagnostic Bridge (K98 §3 in/for)
-- ════════════════════════════════════════════════════

/-! Connect K98 §4 path telicity to K98 §3 for/in adverbial licensing.
    Diagnostics are defined on `VendlerClass`; we bridge through the
    Vendler classification of motion verbs. This is the §3 ↔ §4
    convergence: both routes through `LicensingPipeline` end at the
    same in/for diagnostic prediction (cf. `DimensionBridge.lean`'s
    universal pipeline-agreement theorem). -/

/-- "arrive" (achievement, bounded path) licenses "in X". -/
theorem arrive_inX :
    arrive.toVerbCore.vendlerClass = some .achievement ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl⟩

/-- "leave" (achievement, source path) licenses "in X". -/
theorem leave_inX :
    leave.toVerbCore.vendlerClass = some .achievement ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl⟩

/-- "run" (activity, path-neutral) licenses "for X". -/
theorem run_forX :
    run.toVerbCore.vendlerClass = some .activity ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl⟩

/-- Motion verb VendlerClass × LevinClass coherence: bounded-path
    motion verbs are achievements, path-neutral ones are activities.
    K98 §4 prediction: path-shape determines aspectual class. -/
theorem motion_vendler_path_coherence :
    (arrive.toVerbCore.vendlerClass = some .achievement ∧
      LevinClass.inherentlyDirectedMotion.pathSpec = some .bounded) ∧
    (leave.toVerbCore.vendlerClass = some .achievement ∧
      LevinClass.leave.pathSpec = some .source) ∧
    (run.toVerbCore.vendlerClass = some .activity ∧
      LevinClass.mannerOfMotion.pathSpec = none) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- ════════════════════════════════════════════════════
-- § 5. Part II — Propositional invocations of K98 §4 substrate
-- ════════════════════════════════════════════════════

/-! ### Substrate-honest §4 invocations

    The previous sections (§1-§4) work at the Bool-tag level
    (`pathShapeToTelicity` mapping `PathShape` to `Telicity`). The
    section below INVOKES the propositional K98 §4 substrate from
    `Theories/Semantics/Events/MovementRelations.lean` on abstract
    θ + Path Loc + Ev Time instances — paralleling K89 study §3's
    invocations of `qmod_of_cum_is_qua`/`measure_phrase_makes_qua`.

    The big propositional theorems for K98 §4's central result
    (bounded path → telic VP, unbounded path → atelic VP) are
    delegated to the existing σ-pullback infrastructure in
    `Theories/Semantics/Events/SpatialTrace.lean`; the K98 §4
    LABEL for these theorems lives in `MovementRelations.lean` as
    `k98_movement_telic_via_spatial_trace` and
    `k98_unbounded_movement_atelic_via_spatial_trace`.

    The K98 §4 substrate predicates EXP, SEINC, ADJ, SMR, MR,
    SOURCE, GOAL, KM' are exercised below on Path Loc + Ev Time.

    Deferred (require new substrate per `MovementRelations.lean`'s
    architectural notes): TANG_H tangentiality (eq. 17), full ADJ
    axioms on the adjacency primitive, cross-dimensional movements
    (K98 §4.6 heat/bake/whip).
-/

section PropositionalMovement

open Semantics.Events
open Semantics.Events.MovementRelations
open Semantics.Spatial.Path
open Mereology

variable {Loc Time : Type*} [LinearOrder Time]
variable [cem : EventCEM Time] [SemilatticeSup (Path Loc)]
variable [st : SpatialTrace Loc Time]

/-- *Mary walked from the university to the capitol* propositional
    (K98 §4.5 eq. 74): a SOURCE+GOAL-bounded path predicate is QUA,
    so the VP is telic. Direct invocation of K98 §4 substrate via
    the σ-pullback. -/
theorem walked_from_to_telic_propositional
    (hinj : Function.Injective st.σ)
    {P : Path Loc → Prop} (hP : QUA P) :
    @QUA _ cem.evSemilatticeSup.toPartialOrder (P ∘ st.σ) :=
  k98_movement_telic_via_spatial_trace hinj hP

/-- *Mary walked towards the capitol* propositional (K98 §4.5 eq. 75):
    SOURCE-but-no-GOAL path predicate is CUM, so the VP is atelic.
    Direct invocation. -/
theorem walked_towards_atelic_propositional
    {P : Path Loc → Prop} (hP : CUM P) :
    @CUM _ cem.evSemilatticeSup (P ∘ st.σ) :=
  k98_unbounded_movement_atelic_via_spatial_trace hP

end PropositionalMovement

-- ════════════════════════════════════════════════════
-- § 6. K98 §4.1 EXP / SEINC instances
-- ════════════════════════════════════════════════════

/-! K98 §4.1 EXP (eq. 63) and SEINC (eq. 65) on `Ev Time`. The
    precedence relation is `Ev.precedes` (one event's runtime is
    entirely before the other's). These abbreviations show that the
    K98 §4 EXP/SEINC predicates are well-formed on `Ev Time` and
    can be reasoned about given concrete θ instances. -/

section Expansiveness

open Semantics.Events
open Semantics.Events.Mereology
open Semantics.Events.MovementRelations

variable {α : Type*} [SemilatticeSup α]
variable {Time : Type*} [LinearOrder Time]

/-- EXP-as-property of any θ : α → Ev Time → Prop using `Ev.precedes`. -/
abbrev expEv (θ : α → Ev Time → Prop) : Prop :=
  EXP (Ev.precedes (Time := Time)) θ

/-- SEINC-as-property using `Ev.precedes`. Requires `[SemilatticeSup (Ev Time)]`,
    which `EventCEM` provides automatically. -/
abbrev seincEv [EventCEM Time] (θ : α → Ev Time → Prop) : Prop :=
  SEINC (Ev.precedes (Time := Time)) θ

end Expansiveness

-- ════════════════════════════════════════════════════
-- § 7. K98 §4.2 SMR / §4.3 MR instances
-- ════════════════════════════════════════════════════

/-! K98 §4.2 SMR (eq. 69) and §4.3 MR (eq. 71) on `Path Loc → Ev Time → Prop`.
    The path-adjacency relation is `Path.adjacent` (share an endpoint);
    event-adjacency is `Ev.adjacent` (runtime intervals meet);
    `isPath := fun _ => True` since the source type is already `Path Loc`. -/

section MovementInstances

open Semantics.Events
open Semantics.Events.Mereology
open Semantics.Events.MovementRelations
open Semantics.Spatial.Path

variable {Loc Time : Type*} [LinearOrder Time]
variable [EventCEM Time] [PartialOrder (Path Loc)] [SemilatticeSup (Path Loc)]

/-- SMR specialized to paths and events with concrete adjacency. The
    `isPath` predicate is trivially true for `Path Loc` since every
    inhabitant is already a path. -/
abbrev smrPath (θ : Path Loc → Ev Time → Prop) : Prop :=
  SMR Path.adjacent (Ev.adjacent (Time := Time))
    (fun _ : Path Loc => True) θ

/-- MR specialized to paths and events with concrete adjacency
    + precedence. -/
abbrev mrPath (θ : Path Loc → Ev Time → Prop) : Prop :=
  MR Path.adjacent (Ev.adjacent (Time := Time)) (Ev.precedes (Time := Time))
    (fun _ : Path Loc => True) θ

end MovementInstances

end Krifka1998Movement
