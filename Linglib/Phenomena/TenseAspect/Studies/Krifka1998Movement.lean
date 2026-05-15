import Linglib.Theories.Semantics.Events.SpatialTrace
import Linglib.Theories.Semantics.Events.DimensionBridge
import Linglib.Theories.Semantics.Events.ThematicRoleProperties
import Linglib.Theories.Semantics.Events.EventAdjacency
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

## Two layers of K98 §4 content

**Bool-tag projection (§§ 1–4 below)**: the σ trace function and
`PathShape → Telicity` bridge in `Theories/Semantics/Events/SpatialTrace.lean`
provide the engineering surface — `LevinClass.pathSpec` per-verb
annotations, `LicensingPipeline PathShape` for the in/for diagnostic.

**Propositional K98 §4 substrate (§§ 5–8 below)**: the predicates
EXP (eq. 63), SEINC (eq. 65), ADJ (eq. 68), SMR (eq. 69),
MovementClosure + MR (eq. 71 modulo TANG_H) on abstract θ
instances. Inlined here from the former
`Theories/Semantics/Events/MovementRelations.lean` — that file was a
single-consumer (this file) substrate and an audit against the K98
manuscript found that several of its declarations were misattributed:

- `km'` (claimed K98 eq. 72) was actually a Zwarts/Gawron σ-pullback,
  not K98's per-piece inductive KM'. Dropped.
- `SOURCE`/`GOAL` (claimed K98 eq. 73) were stated as definitions but
  K98 states them as necessary conditions on movement relations. Dropped.
- `k98_movement_telic_via_spatial_trace` /
  `k98_unbounded_movement_atelic_via_spatial_trace` were one-line
  delegates to `SpatialTrace.bounded_path_telic` /
  `SpatialTrace.unbounded_path_atelic` mislabeled as K98 §4 results.
  K98 §4 derives walk-a-kilometer telicity via KM' extensivity +
  tangentiality, not via σ-pullback. The σ-pullback delegates are
  now invoked directly (§ 6 below), without the K98-attribution.

Honestly weakened content retained:

- **TANG_H tangentiality** (K98 eq. 17) on directed paths is omitted
  in `MovementClosure`; the resulting `MR` admits stop-and-go (K98
  70.b), Alcatraz (70.e), and Echternach (70.d) movements (which K98
  also admits) plus telekinetic non-meeting concatenations (which K98
  rules out via TANG_H, eq. 70.c — the discriminating example).

Per K98 §4.6 quality changes (heat, bake, whip — eq. 76-77),
dimensional movements are structurally identical to spatial ones, but
require a `DirectedPath` generalization not formalized here.
K98 §4.7 instantaneous movements (eq. 78, *Mary arrived in London*)
reduce to the bounded-path case at the limit of granularity.

## Structure

1. **§4.5 Source/Goal/Path-Spec verbs** — per-verb path specification
2. **§4 Path → Telicity → Licensing pipeline** — full chain
3. **§4 Motion VP data** — verb + PP pairs with path shapes
4. **§3 ↔ §4 diagnostic bridge** — connect path telicity to for/in licensing
5. **K98 §4 propositional substrate** — EXP/SEINC/ADJ/SMR/MovementClosure/MR
6. **σ-pullback invocations** — bounded/unbounded path → telic/atelic VP
7. **EXP/SEINC instances on `Event Time`**
8. **SMR/MR instances on `Path Loc → Event Time → Prop`**

## Sister files

- `Studies/Krifka1998.lean` — K98 §3 (incrementality through CUM/QUA
  propagation, SINC/INC verb classes); the §3-counterpart to this file
- `Studies/Krifka1989.lean` — K89, the algebraic-mereology antecedent
  with K89 §4 thematic-relation features (table 14)
- `Studies/KennedyLevin2008.lean` — degree achievements (heat, cool,
  dry); K98 §4.6 quality-change movements are the K98-substrate version
  of K&L's degree-of-change account, related but with different primitives

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
-- § 5. K98 §4 propositional substrate
-- ════════════════════════════════════════════════════

/-! Predicates classifying thematic relations θ : α → β → Prop by
    adjacency, precedence, and sub-event/sub-path correspondence.
    Inlined from the former `Theories/Semantics/Events/MovementRelations.lean`
    (single-consumer substrate; K98 misattributions on km'/SOURCE/GOAL/
    bridges dropped — see module docstring).

    Faithful K98 §4 content:
    - **EXP** (eq. 63): temporally-following sub-events ↦ non-overlapping objects
    - **SEINC** (eq. 65): EXP ∧ MO
    - **ADJ** (eq. 68 — modulo an extra `z ≤ x` premise vs the printed
      equation): sub-event temporal adjacency ↔ sub-path spatial adjacency
    - **SMR** (eq. 69): ADJ ∧ MO ∧ path-only first-arg
    - **MovementClosure** + **MR** (eq. 71 modulo TANG_H): inductive
      closure under precedence-respecting sums
-/

section K98PropositionalSubstrate

open Semantics.Events.ThematicRoleProperties (MO)
open Mereology

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

/-- K98 §4.2 eq. 68 ADJ: adjacency property. Whenever two sub-events
    of a movement event are temporally adjacent, their corresponding
    sub-paths are spatially adjacent, and vice versa. -/
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
    under precedence-respecting sums. K98's TANG_H tangentiality clause
    (eq. 17) is OMITTED here — admits stop-and-go, Alcatraz, and
    Echternach movements (also admitted by K98) plus telekinetic
    non-meeting concatenations (which K98 rules out via TANG_H,
    eq. 70.c). Adding TANG_H requires a directed-path substrate. -/
inductive MovementClosure {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (precedes : β → β → Prop) (θ' : α → β → Prop) : α → β → Prop where
  | base {x : α} {e : β} : θ' x e → MovementClosure precedes θ' x e
  | sum {x1 x2 : α} {e1 e2 : β} :
      MovementClosure precedes θ' x1 e1 →
      MovementClosure precedes θ' x2 e2 →
      precedes e1 e2 →
      MovementClosure precedes θ' (x1 ⊔ x2) (e1 ⊔ e2)

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
    MR adjα adjβ precedes isPath θ := by
  refine ⟨θ, h, fun x e => ⟨MovementClosure.base, ?_⟩⟩
  intro hcl
  induction hcl with
  | base h => exact h
  | sum _ _ hprec ih1 ih2 => exact hClosed _ _ _ _ ih1 ih2 hprec

end K98PropositionalSubstrate

-- ════════════════════════════════════════════════════
-- § 6. σ-pullback invocations (bounded/unbounded path → telic/atelic VP)
-- ════════════════════════════════════════════════════

/-! Invokes `SpatialTrace.bounded_path_telic` / `unbounded_path_atelic`
    on abstract θ + Path Loc + Event Time instances. These are the
    σ-pullback theorems; K98 §4 derives walk-a-kilometer telicity
    differently (via KM' extensivity + tangentiality), so the
    K98-flavored attribution that the former
    `MovementRelations.lean` placed on these calls has been removed. -/

section SpatialTracePullback

open Semantics.Events
open Semantics.Spatial.Path
open Mereology

variable {Loc Time : Type*} [LinearOrder Time]
variable [cem : EventCEM Time] [SemilatticeSup (Path Loc)]
variable [st : SpatialTrace Loc Time]

/-- Bounded path predicate (QUA) ↦ telic VP (QUA on events) via the
    σ-pullback. Used to back the K98 §4.5 *walked from X to Y* analysis
    at the Bool-tag level (§ 2). -/
theorem walked_from_to_telic_propositional
    (hinj : Function.Injective st.σ)
    {P : Path Loc → Prop} (hP : QUA P) :
    @QUA _ cem.evSemilatticeSup.toPartialOrder (P ∘ st.σ) :=
  SpatialTrace.bounded_path_telic hinj hP

/-- Unbounded path predicate (CUM) ↦ atelic VP (CUM on events) via the
    σ-pullback. Used to back the K98 §4.5 *walked towards X* analysis
    at the Bool-tag level (§ 2). -/
theorem walked_towards_atelic_propositional
    {P : Path Loc → Prop} (hP : CUM P) :
    @CUM _ cem.evSemilatticeSup (P ∘ st.σ) :=
  SpatialTrace.unbounded_path_atelic hP

end SpatialTracePullback

-- ════════════════════════════════════════════════════
-- § 7. K98 §4.1 EXP / SEINC instances on `Event Time`
-- ════════════════════════════════════════════════════

/-! K98 §4.1 EXP (eq. 63) and SEINC (eq. 65) instantiated on `Event Time`
    via `Event.precedes`. These abbreviations show that the K98 §4
    EXP/SEINC predicates are well-formed on `Event Time` and can be
    reasoned about given concrete θ instances. -/

section Expansiveness

open Semantics.Events
open Semantics.Events.Mereology

variable {α : Type*} [SemilatticeSup α]
variable {Time : Type*} [LinearOrder Time]

/-- EXP-as-property of any θ : α → Event Time → Prop using `Event.precedes`. -/
abbrev expEv (θ : α → Event Time → Prop) : Prop :=
  EXP (Event.precedes (Time := Time)) θ

/-- SEINC-as-property using `Event.precedes`. Requires `[SemilatticeSup (Event Time)]`,
    which `EventCEM` provides automatically. -/
abbrev seincEv [EventCEM Time] (θ : α → Event Time → Prop) : Prop :=
  SEINC (Event.precedes (Time := Time)) θ

end Expansiveness

-- ════════════════════════════════════════════════════
-- § 8. K98 §4.2 SMR / §4.3 MR instances on `Path Loc → Event Time → Prop`
-- ════════════════════════════════════════════════════

/-! K98 §4.2 SMR (eq. 69) and §4.3 MR (eq. 71) instantiated with concrete
    adjacency. The path-adjacency relation is `Path.adjacent` (share an
    endpoint); event-adjacency is `Event.adjacent` (runtime intervals meet);
    `isPath := fun _ => True` since the source type is already `Path Loc`. -/

section MovementInstances

open Semantics.Events
open Semantics.Events.Mereology
open Semantics.Spatial.Path

variable {Loc Time : Type*} [LinearOrder Time]
variable [EventCEM Time] [PartialOrder (Path Loc)] [SemilatticeSup (Path Loc)]

/-- SMR specialized to paths and events with concrete adjacency. The
    `isPath` predicate is trivially true for `Path Loc` since every
    inhabitant is already a path. -/
abbrev smrPath (θ : Path Loc → Event Time → Prop) : Prop :=
  SMR Path.adjacent (Event.adjacent (Time := Time))
    (fun _ : Path Loc => True) θ

/-- MR specialized to paths and events with concrete adjacency
    + precedence. -/
abbrev mrPath (θ : Path Loc → Event Time → Prop) : Prop :=
  MR Path.adjacent (Event.adjacent (Time := Time)) (Event.precedes (Time := Time))
    (fun _ : Path Loc => True) θ

end MovementInstances

end Krifka1998Movement
