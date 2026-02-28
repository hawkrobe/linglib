import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Semantics.Events.SpatialTrace
import Linglib.Phenomena.TenseAspect.DiagnosticsBridge
import Linglib.Phenomena.TenseAspect.Bridge.GradualChange
import Linglib.Phenomena.TenseAspect.Bridge.Krifka1989
import Linglib.Phenomena.Plurals.Bridge.StratifiedReference

/-!
# Cross-Bridge Consistency Tests

Verifies that all bridge files agree on fragment verb classifications.
Each verb that appears in multiple bridges gets a single theorem here
checking that its vendlerClass, verbIncClass, and levinClass fields
yield consistent licensing predictions across all classification paths.

## What it catches

If you change a fragment verb annotation (e.g., `eat.vendlerClass`
from `.accomplishment` to `.activity`), the per-bridge theorems in
each bridge file break individually. But this file additionally
verifies that the *cross-cutting invariants* hold:

- vendlerClass and verbIncClass agree on telicity
- vendlerClass and levinClass agree on path/telicity
- predictsGRAD and predictsSSR are complementary for the same verb
- All classification paths (VendlerClass, Telicity, MereoTag,
  Boundedness) converge at the same licensing prediction
-/

namespace Phenomena.TenseAspect.Bridge.CrossBridgeConsistency

open Fragments.English.Predicates.Verbal
open Semantics.Lexical.Verb.Aspect (VendlerClass Telicity)
open Semantics.Events.Krifka1998 (VerbIncClass)
open Core.Scale (LicensingPipeline Boundedness MereoTag)
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction)
open Phenomena.TenseAspect.Bridge.GradualChange (predictsGRAD)
open Phenomena.Plurals.Bridge.StratifiedReference (predictsSSR)
open Core.Path (PathShape)

-- ════════════════════════════════════════════════════
-- § 1. VendlerClass × VerbIncClass Consistency
-- ════════════════════════════════════════════════════

/-! Sinc/inc verbs should be accomplishments (telic with incremental theme).
    CumOnly verbs should be activities (atelic, no theme-event mapping).
    Intransitives (no verbIncClass) can be any class. -/

/-- "eat": accomplishment + sinc → telic VP with incremental theme. -/
theorem eat_vendler_inc_consistent :
    eat.toVerbCore.vendlerClass = some .accomplishment ∧
    eat.toVerbCore.verbIncClass = some .sinc ∧
    VendlerClass.accomplishment.telicity = .telic := ⟨rfl, rfl, rfl⟩

/-- "build": accomplishment + sinc → telic VP with incremental theme. -/
theorem build_vendler_inc_consistent :
    build.toVerbCore.vendlerClass = some .accomplishment ∧
    build.toVerbCore.verbIncClass = some .sinc ∧
    VendlerClass.accomplishment.telicity = .telic := ⟨rfl, rfl, rfl⟩

/-- "read": accomplishment + inc → telic VP with incremental (non-strict) theme. -/
theorem read_vendler_inc_consistent :
    read.toVerbCore.vendlerClass = some .accomplishment ∧
    read.toVerbCore.verbIncClass = some .inc ∧
    VendlerClass.accomplishment.telicity = .telic := ⟨rfl, rfl, rfl⟩

/-- "push": activity + cumOnly → atelic VP, no theme-event mapping. -/
theorem push_vendler_inc_consistent :
    push.toVerbCore.vendlerClass = some .activity ∧
    push.toVerbCore.verbIncClass = some .cumOnly ∧
    VendlerClass.activity.telicity = .atelic := ⟨rfl, rfl, rfl⟩

/-- "kick": activity + no verbIncClass → atelic, no incremental theme. -/
theorem kick_vendler_inc_consistent :
    kick.toVerbCore.vendlerClass = some .activity ∧
    kick.toVerbCore.verbIncClass = none ∧
    VendlerClass.activity.telicity = .atelic := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. GRAD × SSR Complementarity
-- ════════════════════════════════════════════════════

/-! GRAD (gradual change) is predicted for sinc/inc verbs, which are
    accomplishments (telic). SSR (subinterval reference) is predicted
    for states/activities (atelic). These should be complementary:
    a verb should not predict both GRAD and SSR. -/

/-- "eat": GRAD ✓, SSR ✗ (accomplishment, sinc). -/
theorem eat_grad_ssr_complementary :
    predictsGRAD eat.toVerbCore.verbIncClass = true ∧
    predictsSSR eat.toVerbCore.vendlerClass = false := ⟨rfl, rfl⟩

/-- "build": GRAD ✓, SSR ✗ (accomplishment, sinc). -/
theorem build_grad_ssr_complementary :
    predictsGRAD build.toVerbCore.verbIncClass = true ∧
    predictsSSR build.toVerbCore.vendlerClass = false := ⟨rfl, rfl⟩

/-- "read": GRAD ✓, SSR ✗ (accomplishment, inc). -/
theorem read_grad_ssr_complementary :
    predictsGRAD read.toVerbCore.verbIncClass = true ∧
    predictsSSR read.toVerbCore.vendlerClass = false := ⟨rfl, rfl⟩

/-- "push": GRAD ✗, SSR ✓ (activity, cumOnly). -/
theorem push_grad_ssr_complementary :
    predictsGRAD push.toVerbCore.verbIncClass = false ∧
    predictsSSR push.toVerbCore.vendlerClass = true := ⟨rfl, rfl⟩

/-- "sleep": GRAD ✗, SSR ✓ (state, no incremental theme). -/
theorem sleep_grad_ssr_complementary :
    predictsGRAD sleep.toVerbCore.verbIncClass = false ∧
    predictsSSR sleep.toVerbCore.vendlerClass = true := ⟨rfl, rfl⟩

/-- "run": GRAD ✗, SSR ✓ (activity, no incremental theme). -/
theorem run_grad_ssr_complementary :
    predictsGRAD run.toVerbCore.verbIncClass = false ∧
    predictsSSR run.toVerbCore.vendlerClass = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Full Licensing Pipeline Convergence Per Verb
-- ════════════════════════════════════════════════════

/-! For each shared verb, verify the complete chain from fragment
    annotation through all classification levels to licensing and
    diagnostic predictions. Changing any fragment field breaks the
    entire chain for that verb. -/

/-- "eat": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem eat_full_pipeline :
    eat.toVerbCore.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "arrive": achievement → telic → QUA → closed → licensed → "in X" ✓. -/
theorem arrive_full_pipeline :
    arrive.toVerbCore.vendlerClass = some .achievement ∧
    VendlerClass.achievement.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "sleep": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem sleep_full_pipeline :
    sleep.toVerbCore.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "run": activity → atelic → CUM → open → blocked → "for X" ✓. -/
theorem run_full_pipeline :
    run.toVerbCore.vendlerClass = some .activity ∧
    VendlerClass.activity.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "see": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem see_full_pipeline :
    see.toVerbCore.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "leave": achievement → telic → QUA → closed → licensed → "in X" ✓. -/
theorem leave_full_pipeline :
    leave.toVerbCore.vendlerClass = some .achievement ∧
    VendlerClass.achievement.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "kill": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem kill_full_pipeline :
    kill.toVerbCore.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Motion Verb Cross-Classification
-- ════════════════════════════════════════════════════

/-! Motion verbs have both vendlerClass and levinClass annotations.
    Verify these are consistent: inherently-directed-motion verbs
    (achievements) have bounded paths, manner-of-motion verbs
    (activities) have no inherent path. -/

/-- "arrive": achievement + inherentlyDirectedMotion + bounded path. -/
theorem arrive_motion_consistent :
    arrive.toVerbCore.vendlerClass = some .achievement ∧
    arrive.toVerbCore.levinClass = some .inherentlyDirectedMotion ∧
    LevinClass.inherentlyDirectedMotion.pathSpec = some .bounded := ⟨rfl, rfl, rfl⟩

/-- "leave": achievement + leave class + source path. -/
theorem leave_motion_consistent :
    leave.toVerbCore.vendlerClass = some .achievement ∧
    leave.toVerbCore.levinClass = some .leave ∧
    LevinClass.leave.pathSpec = some .source := ⟨rfl, rfl, rfl⟩

/-- "run": activity + mannerOfMotion + no inherent path. -/
theorem run_motion_consistent :
    run.toVerbCore.vendlerClass = some .activity ∧
    run.toVerbCore.levinClass = some .mannerOfMotion ∧
    LevinClass.mannerOfMotion.pathSpec = none := ⟨rfl, rfl, rfl⟩

end Phenomena.TenseAspect.Bridge.CrossBridgeConsistency
