import Linglib.Theories.Semantics.Events.SpatialTrace
import Linglib.Theories.Semantics.Events.ThematicRoleProperties
import Linglib.Theories.Semantics.Events.EventAdjacency
import Linglib.Theories.Semantics.Events.PrecedenceClosure
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.TenseAspect.Diagnostics

/-!
# @cite{krifka-1998} §4: Telicity by Precedence and Adjacency

K98's distinctive contribution beyond K89: the path/movement extension of
mereological telicity. §4 derives telicity from spatial and dimensional
**paths** — a movement event is telic iff its path is bounded. The
incrementality side (K98 §3, CUM/QUA propagation through SINC verbs) is
covered by sister file `Studies/Krifka1998.lean`.

The file has two layers. **Bool-tag layer** (§§ 1–4) uses the σ-trace
infrastructure in `Theories/Semantics/Events/SpatialTrace.lean` plus the
`LevinClass.pathSpec` per-verb annotations to get `LicensingPipeline
PathShape` for the in/for diagnostic. **Propositional layer** (§§ 5–8)
contains the K98 §4 predicates (EXP eq. 63, SEINC eq. 65, ADJ eq. 68,
SMR eq. 69, MovementClosure + MR eq. 71) on abstract θ instances,
inlined here from the former single-consumer
`Theories/Semantics/Events/MovementRelations.lean`.

## Main definitions

* `EXP` / `SEINC` / `ADJ` / `SMR` — K98 §4 propositional predicates
* `MovementClosure` / `MR` — K98 §4.3 closure substrate (TANG_H-free)
* `expEv` / `seincEv` / `smrPath` / `mrPath` — `Event Time` instantiations
* `MotionVPDatum` / `motionData` — Bool-tag-level VP data + drift sentries
* `walked_from_to_telic_propositional` / `walked_towards_atelic_propositional` —
  σ-pullback theorems backing the Bool-tag pipeline

## TODO

* **TANG_H tangentiality** (K98 eq. 17) on directed paths. Without it,
  `MR` admits telekinetic non-meeting concatenations (K98 eq. 70.c) that
  K98 explicitly rules out. Adding TANG_H requires a `DirectedPath`
  substrate not yet in linglib.
* **Cross-dimensional movements** (K98 §4.6: heat, bake, whip — eq. 76-77).
  Structurally identical to spatial movements but require the same
  `DirectedPath` generalization.
* **Full ADJ axioms** on adjacency (K98 §2.3 eq. 14.b: adjacency-doesn't-
  overlap, adjacency-propagates-under-part). The concrete `Path.adjacent`
  + `Event.adjacent` satisfy these but the propositional theorems are
  not added.

## References

* @cite{krifka-1998} §4 (Telicity by Precedence and Adjacency)
* Sister: `Studies/Krifka1998.lean` (K98 §3), `Studies/Krifka1989.lean` (K89),
  `Studies/KennedyLevin2008.lean` (K98 §4.6 ≈ K&L's degree-of-change account)
-/

namespace Krifka1998Movement

open Semantics.Verb (LevinClass MeaningComponents)
open Fragments.English.Predicates.Verbal
open Semantics.Events.SpatialTrace (pathShapeToTelicity)
open Semantics.Verb
open Features
open Semantics.Spatial.Path (PathShape)
open Core.Scale (LicensingPipeline)
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction)

/-! ### Per-verb path specification (K98 §4.5 eq. 73) -/

/-- "arrive" is inherently directed motion (K98 §4.7 eq. 78). -/
theorem arrive_levinClass :
    arrive.toVerbCore.levinClass = some .inherentlyDirectedMotion := rfl

/-- Inherently directed motion → bounded path (K98 §4.5 GOAL specified). -/
theorem arrive_pathSpec :
    LevinClass.inherentlyDirectedMotion.pathSpec = some .bounded := rfl

/-- "leave" is a leave verb (K98 §4.5 SOURCE-only). -/
theorem leave_levinClass :
    leave.toVerbCore.levinClass = some .leave := rfl

/-- Leave verbs → source path. -/
theorem leave_pathSpec :
    LevinClass.leave.pathSpec = some .source := rfl

/-- "run" is manner-of-motion (K98 §4.5 path-neutral; PP supplies path). -/
theorem run_levinClass :
    run.toVerbCore.levinClass = some .mannerOfMotion := rfl

/-- Manner-of-motion verbs are path-neutral (path comes from PP). -/
theorem run_pathSpec :
    LevinClass.mannerOfMotion.pathSpec = none := rfl

-- Fragment-grounding drift sentries: changing a fragment annotation in
-- `Fragments/English/Predicates/Verbal.lean` breaks exactly one theorem.

/-- *eat* is annotated as SINC verb-incrementality class. -/
theorem eat_verbIncClass_sinc :
    eat.toVerbCore.verbIncClass = some .sinc := rfl

/-- *arrive* is annotated as an achievement Vendler class. -/
theorem arrive_vendlerClass_achievement :
    arrive.toVerbCore.vendlerClass = some .achievement := rfl

/-- *sleep* is annotated as a state Vendler class. -/
theorem sleep_vendlerClass_state :
    sleep.toVerbCore.vendlerClass = some .state := rfl

/-! ### PathShape → Telicity → Licensing (K98 §4 MR eq. 71) -/

/-- Bounded path → telic → licensed. K98 §4 eq. 74 *walked from X to Y*. -/
theorem bounded_pipeline :
    pathShapeToTelicity .bounded = .telic ∧
    LicensingPipeline.isLicensed PathShape.bounded = true := ⟨rfl, rfl⟩

/-- Source path → telic → licensed. K98 §4 eq. 73 *Mary left the house*. -/
theorem source_pipeline :
    pathShapeToTelicity .source = .telic ∧
    LicensingPipeline.isLicensed PathShape.source = true := ⟨rfl, rfl⟩

/-- Unbounded path → atelic → blocked. K98 §4 eq. 75 *walked towards X*. -/
theorem unbounded_pipeline :
    pathShapeToTelicity .unbounded = .atelic ∧
    LicensingPipeline.isLicensed PathShape.unbounded = false := ⟨rfl, rfl⟩

/-! ### Motion VP data (K98 §4.5 eq. 74-75) -/

/-- A motion VP datum: verb + PP + path shape + expected telicity. -/
structure MotionVPDatum where
  verb : String
  pp : String
  pathShape : PathShape
  expectedTelicity : Telicity
  deriving Repr, DecidableEq

/-- "arrive at the store" — bounded → telic → "in X" ✓. K98 §4.7 eq. 78. -/
def arriveAtStore : MotionVPDatum :=
  { verb := "arrive", pp := "at the store",
    pathShape := .bounded, expectedTelicity := .telic }

/-- "leave the house" — source → telic → "in X" ✓. K98 §4.5 eq. 73. -/
def leaveTheHouse : MotionVPDatum :=
  { verb := "leave", pp := "the house",
    pathShape := .source, expectedTelicity := .telic }

/-- "run to the park" — manner + bounded PP → telic → "in X" ✓. K98 eq. 74. -/
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

/-! ### §3 ↔ §4 diagnostic bridge (K98 §3 in/for) -/

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

/-- Motion verb VendlerClass × LevinClass coherence: bounded-path motion
    verbs are achievements, path-neutral ones are activities. -/
theorem motion_vendler_path_coherence :
    (arrive.toVerbCore.vendlerClass = some .achievement ∧
      LevinClass.inherentlyDirectedMotion.pathSpec = some .bounded) ∧
    (leave.toVerbCore.vendlerClass = some .achievement ∧
      LevinClass.leave.pathSpec = some .source) ∧
    (run.toVerbCore.vendlerClass = some .activity ∧
      LevinClass.mannerOfMotion.pathSpec = none) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ### K98 §4 propositional substrate -/

section K98PropositionalSubstrate

open Semantics.Events.ThematicRoleProperties (MO)
open _root_.Mereology

/-- K98 §4.1 eq. 63 EXP: expansion. If x is θ-related to e and y to a
    temporally-following e', then x and y do not overlap. -/
def EXP {α β : Type*} [SemilatticeSup α]
    (precedes : β → β → Prop) (θ : α → β → Prop) : Prop :=
  ∀ (x y : α) (e e' : β),
    θ x e → θ y e' → precedes e e' → ¬ Overlap x y

/-- K98 §4.1 eq. 65 SEINC: strictly expansive incremental. EXP ∧ MO. -/
def SEINC {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (precedes : β → β → Prop) (θ : α → β → Prop) : Prop :=
  EXP precedes θ ∧ MO θ

/-- K98 §4.2 eq. 68 ADJ: temporal adjacency on sub-events ↔ spatial
    adjacency on sub-paths. The Lean form adds extra `z ≤ x` and
    `e'' ≤ e` premises vs the printed equation. -/
def ADJ {α β : Type*} [PartialOrder α] [PartialOrder β]
    (adjα : α → α → Prop) (adjβ : β → β → Prop)
    (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (y z : α) (e' e'' : β),
    θ x e → e' ≤ e → e'' ≤ e → y ≤ x → z ≤ x →
    θ y e' → θ z e'' → (adjβ e' e'' ↔ adjα y z)

/-- K98 §4.2 eq. 69 SMR: ADJ + MO + first-arg constrained to paths. -/
def SMR {α β : Type*} [PartialOrder α] [PartialOrder β]
    [SemilatticeSup α] [SemilatticeSup β]
    (adjα : α → α → Prop) (adjβ : β → β → Prop)
    (isPath : α → Prop) (θ : α → β → Prop) : Prop :=
  ADJ adjα adjβ θ ∧ MO θ ∧ ∀ x e, θ x e → isPath x

/-- K98 §4.3 eq. 71 closure: smallest relation containing θ' and closed
    under precedence-respecting sums. K98's TANG_H clause (eq. 17) is
    OMITTED — see module TODO. Specialization of
    `Semantics.Events.PrecedenceClosure` with `cond := precedes`. -/
abbrev MovementClosure {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (precedes : β → β → Prop) (θ' : α → β → Prop) : α → β → Prop :=
  Semantics.Events.PrecedenceClosure precedes θ'

/-- K98 §4.3 eq. 71 MR (TANG_H-free): θ is a movement relation iff
    there exists an SMR θ' such that θ is the `MovementClosure` of θ'. -/
def MR {α β : Type*} [PartialOrder α] [PartialOrder β]
    [SemilatticeSup α] [SemilatticeSup β]
    (adjα : α → α → Prop) (adjβ : β → β → Prop) (precedes : β → β → Prop)
    (isPath : α → Prop) (θ : α → β → Prop) : Prop :=
  ∃ θ' : α → β → Prop,
    SMR adjα adjβ isPath θ' ∧
    ∀ x e, θ x e ↔ MovementClosure precedes θ' x e

/-- Every SMR is itself an MR, given closure under precedence-respecting sums. -/
theorem mr_of_smr {α β : Type*} [PartialOrder α] [PartialOrder β]
    [SemilatticeSup α] [SemilatticeSup β]
    {adjα : α → α → Prop} {adjβ : β → β → Prop} {precedes : β → β → Prop}
    {isPath : α → Prop} {θ : α → β → Prop}
    (h : SMR adjα adjβ isPath θ)
    (hClosed : ∀ x1 x2 e1 e2, θ x1 e1 → θ x2 e2 → precedes e1 e2 →
               θ (x1 ⊔ x2) (e1 ⊔ e2)) :
    MR adjα adjβ precedes isPath θ :=
  ⟨θ, h, fun x e => ⟨Semantics.Events.PrecedenceClosure.base,
    fun hcl => Semantics.Events.PrecedenceClosure.closure_subset
      (fun _ _ h => h) hClosed hcl⟩⟩

end K98PropositionalSubstrate

/-! ### σ-pullback invocations (bounded/unbounded path → telic/atelic VP) -/

section SpatialTracePullback

open Semantics.Events
open Semantics.Events.CEM
open Semantics.Spatial.Path
open _root_.Mereology

variable {Loc Time : Type*} [LinearOrder Time]
variable [cem : EventCEM Time] [SemilatticeSup (Path Loc)]
variable [st : SpatialTrace Loc Time]

/-- Bounded path predicate (QUA) ↦ telic VP via the σ-pullback. Backs
    the K98 §4.5 *walked from X to Y* analysis at the Bool-tag level. -/
theorem walked_from_to_telic_propositional
    (hinj : Function.Injective st.σ)
    {P : Path Loc → Prop} (hP : QUA P) :
    @QUA _ cem.evSemilatticeSup.toPartialOrder (P ∘ st.σ) :=
  SpatialTrace.bounded_path_telic hinj hP

/-- Unbounded path predicate (CUM) ↦ atelic VP via the σ-pullback. Backs
    the K98 §4.5 *walked towards X* analysis at the Bool-tag level. -/
theorem walked_towards_atelic_propositional
    {P : Path Loc → Prop} (hP : CUM P) :
    @CUM _ cem.evSemilatticeSup (P ∘ st.σ) :=
  SpatialTrace.unbounded_path_atelic hP

end SpatialTracePullback

/-! ### EXP / SEINC instances on `Event Time` (K98 §4.1) -/

section Expansiveness

open Semantics.Events
open Semantics.Events.CEM

variable {α : Type*} [SemilatticeSup α]
variable {Time : Type*} [LinearOrder Time]

/-- EXP-as-property of any θ : α → Event Time → Prop using `Event.precedes`. -/
abbrev expEv (θ : α → Event Time → Prop) : Prop :=
  EXP (Event.precedes (Time := Time)) θ

/-- SEINC-as-property using `Event.precedes`. `EventCEM` provides the
    required `[SemilatticeSup (Event Time)]`. -/
abbrev seincEv [EventCEM Time] (θ : α → Event Time → Prop) : Prop :=
  SEINC (Event.precedes (Time := Time)) θ

end Expansiveness

/-! ### SMR / MR instances on `Path Loc → Event Time → Prop` (K98 §4.2-4.3) -/

section MovementInstances

open Semantics.Events
open Semantics.Events.CEM
open Semantics.Spatial.Path

variable {Loc Time : Type*} [LinearOrder Time]
variable [EventCEM Time] [PartialOrder (Path Loc)] [SemilatticeSup (Path Loc)]

/-- SMR specialized to paths and events with concrete adjacency. -/
abbrev smrPath (θ : Path Loc → Event Time → Prop) : Prop :=
  SMR Path.adjacent (Event.adjacent (Time := Time))
    (fun _ : Path Loc => True) θ

/-- MR specialized to paths and events with concrete adjacency + precedence. -/
abbrev mrPath (θ : Path Loc → Event Time → Prop) : Prop :=
  MR Path.adjacent (Event.adjacent (Time := Time)) (Event.precedes (Time := Time))
    (fun _ : Path Loc => True) θ

end MovementInstances

end Krifka1998Movement
