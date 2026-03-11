import Linglib.Theories.Semantics.Events.SpatialTrace
import Linglib.Theories.Semantics.Events.DimensionBridge
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.TenseAspect.Studies.Rothstein2004

/-!
# Spatial Trace Bridge: Path Telicity → Fragment Verbs

Connects the spatial dimension theory (`Events/SpatialTrace.lean`,
`Events/DimensionBridge.lean`) to concrete motion verb entries in
`Fragments/English/Predicates/Verbal.lean` and telicity diagnostics.

## What it exercises

- `pathShapeToTelicity` (PathShape → Telicity)
- `LevinClass.pathSpec` (verb → path specification)
- `LicensingPipeline PathShape` (bounded → licensed, unbounded → blocked)
- `telicity_boundedness_agree` (PathShape telicity ↔ boundedness licensing)

## Structure

1. **Per-verb path specification** — verify `levinClass.pathSpec` for motion verbs
2. **PathShape → Telicity → Licensing pipeline** — full chain verification
3. **Motion VP telicity data** — verb + PP pairs with path shapes
4. **Diagnostic bridge** — connect path telicity to for/in compatibility
-/

namespace Phenomena.TenseAspect.Studies.SpatialTrace

open Fragments.English.Predicates.Verbal
open Semantics.Events.SpatialTrace (pathShapeToTelicity)
open Semantics.Tense.Aspect.LexicalAspect (VendlerClass Telicity)
open Core.Path (PathShape)
open Core.Scale (LicensingPipeline)
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction)

-- ════════════════════════════════════════════════════
-- § 1. Per-Verb Path Specification Verification
-- ════════════════════════════════════════════════════

/-! Each motion verb's `levinClass` and `pathSpec` annotation is verified
    by `rfl`. Changing any annotation breaks exactly one theorem here. -/

/-- "arrive" is inherently directed motion. -/
theorem arrive_levinClass :
    arrive.toVerbCore.levinClass = some .inherentlyDirectedMotion := rfl

/-- Inherently directed motion → bounded path. -/
theorem arrive_pathSpec :
    LevinClass.inherentlyDirectedMotion.pathSpec = some .bounded := rfl

/-- "leave" is a leave verb. -/
theorem leave_levinClass :
    leave.toVerbCore.levinClass = some .leave := rfl

/-- Leave verbs → source path. -/
theorem leave_pathSpec :
    LevinClass.leave.pathSpec = some .source := rfl

/-- "run" is manner-of-motion. -/
theorem run_levinClass :
    run.toVerbCore.levinClass = some .mannerOfMotion := rfl

/-- Manner-of-motion verbs are path-neutral (path from PP). -/
theorem run_pathSpec :
    LevinClass.mannerOfMotion.pathSpec = none := rfl

-- ════════════════════════════════════════════════════
-- § 2. PathShape → Telicity → Licensing Pipeline
-- ════════════════════════════════════════════════════

/-! The full chain from PathShape through Telicity to licensing is
    verified for all three shapes. The LicensingPipeline instance
    for PathShape is in DimensionBridge.lean. -/

/-- Bounded path → telic → QUA → closed → licensed. -/
theorem bounded_pipeline :
    pathShapeToTelicity .bounded = .telic ∧
    LicensingPipeline.isLicensed PathShape.bounded = true := ⟨rfl, rfl⟩

/-- Source path → telic → QUA → closed → licensed. -/
theorem source_pipeline :
    pathShapeToTelicity .source = .telic ∧
    LicensingPipeline.isLicensed PathShape.source = true := ⟨rfl, rfl⟩

/-- Unbounded path → atelic → CUM → open → blocked. -/
theorem unbounded_pipeline :
    pathShapeToTelicity .unbounded = .atelic ∧
    LicensingPipeline.isLicensed PathShape.unbounded = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Motion VP Telicity Data
-- ════════════════════════════════════════════════════

/-- A motion VP datum: verb + PP + path shape + expected telicity. -/
structure MotionVPDatum where
  verb : String
  pp : String
  pathShape : PathShape
  expectedTelicity : Telicity
  deriving Repr, DecidableEq, BEq

/-- "arrive at the store" — inherently bounded → telic → "in X" ✓ -/
def arriveAtStore : MotionVPDatum :=
  { verb := "arrive", pp := "at the store",
    pathShape := .bounded, expectedTelicity := .telic }

/-- "leave the house" — source → telic → "in X" ✓ -/
def leaveTheHouse : MotionVPDatum :=
  { verb := "leave", pp := "the house",
    pathShape := .source, expectedTelicity := .telic }

/-- "run to the park" — manner + bounded PP → telic → "in X" ✓ -/
def runToThePark : MotionVPDatum :=
  { verb := "run", pp := "to the park",
    pathShape := .bounded, expectedTelicity := .telic }

/-- "run towards the park" — manner + unbounded PP → atelic → "for X" ✓ -/
def runTowardsThePark : MotionVPDatum :=
  { verb := "run", pp := "towards the park",
    pathShape := .unbounded, expectedTelicity := .atelic }

def motionData : List MotionVPDatum :=
  [arriveAtStore, leaveTheHouse, runToThePark, runTowardsThePark]

/-- Path shape determines telicity for all motion data. -/
theorem all_motion_data_correct :
    motionData.all (λ d =>
      pathShapeToTelicity d.pathShape == d.expectedTelicity) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 4. Diagnostic Bridge
-- ════════════════════════════════════════════════════

/-! Connect path telicity to for/in adverbial compatibility.
    Since diagnostics are defined on VendlerClass, we bridge through
    the Vendler classification of motion verbs. -/

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

/-- Motion verb Vendler class × path shape coherence:
    bounded-path motion verbs are achievements, path-neutral ones are activities. -/
theorem motion_vendler_path_coherence :
    (arrive.toVerbCore.vendlerClass = some .achievement ∧
      LevinClass.inherentlyDirectedMotion.pathSpec = some .bounded) ∧
    (leave.toVerbCore.vendlerClass = some .achievement ∧
      LevinClass.leave.pathSpec = some .source) ∧
    (run.toVerbCore.vendlerClass = some .activity ∧
      LevinClass.mannerOfMotion.pathSpec = none) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Phenomena.TenseAspect.Studies.SpatialTrace
