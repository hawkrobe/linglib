import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Semantics.Events.SpatialTrace
import Linglib.Theories.Semantics.Lexical.Verb.DegreeAchievement
import Linglib.Phenomena.TenseAspect.Studies.Rothstein2004
import Linglib.Phenomena.TenseAspect.Studies.Krifka1998
import Linglib.Phenomena.TenseAspect.Studies.Krifka1989
import Linglib.Phenomena.Plurals.Studies.Champollion2017

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

namespace Phenomena.TenseAspect.Studies.AspectualConsistency

open Fragments.English.Predicates.Verbal
open Semantics.Tense.Aspect.LexicalAspect (VendlerClass Telicity)
open Semantics.Events.Krifka1998 (VerbIncClass)
open Core.Scale (LicensingPipeline Boundedness MereoTag)
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction)
open Phenomena.TenseAspect.Studies.Krifka1998 (predictsGRAD)
open Phenomena.Plurals.Studies.Champollion2017 (predictsSSR)
open Core.Path (PathShape)
open Semantics.Lexical.Verb.DegreeAchievement (DegreeAchievementScale)

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

-- Accomplishment verbs (telic, "in X")

/-- "give": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem give_full_pipeline :
    give.toVerbCore.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "cover": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem cover_full_pipeline :
    cover.toVerbCore.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "buy": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem buy_full_pipeline :
    buy.toVerbCore.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "sell": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem sell_full_pipeline :
    sell.toVerbCore.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "break": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem break_full_pipeline :
    break_.toVerbCore.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "tear": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem tear_full_pipeline :
    tear_.toVerbCore.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "burn": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem burn_full_pipeline :
    burn.toVerbCore.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "destroy": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem destroy_full_pipeline :
    destroy.toVerbCore.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "melt": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem melt_full_pipeline :
    melt.toVerbCore.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Achievement verbs (telic, "in X")

/-- "put": achievement → telic → QUA → closed → licensed → "in X" ✓. -/
theorem put_full_pipeline :
    put.toVerbCore.vendlerClass = some .achievement ∧
    VendlerClass.achievement.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "meet": achievement → telic → QUA → closed → licensed → "in X" ✓. -/
theorem meet_full_pipeline :
    meet.toVerbCore.vendlerClass = some .achievement ∧
    VendlerClass.achievement.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.isLicensed Boundedness.closed = true ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Activity verbs (atelic, "for X")

/-- "chase": activity → atelic → CUM → open → blocked → "for X" ✓. -/
theorem chase_full_pipeline :
    chase.toVerbCore.vendlerClass = some .activity ∧
    VendlerClass.activity.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "hit": activity → atelic → CUM → open → blocked → "for X" ✓. -/
theorem hit_full_pipeline :
    hit.toVerbCore.vendlerClass = some .activity ∧
    VendlerClass.activity.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- State verbs (atelic, "for X")

/-- "weigh": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem weigh_full_pipeline :
    weigh.toVerbCore.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "measure": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem measure_full_pipeline :
    measure.toVerbCore.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "enjoy": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem enjoy_full_pipeline :
    enjoy.toVerbCore.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "like": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem like_full_pipeline :
    like.toVerbCore.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "hate": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem hate_full_pipeline :
    hate.toVerbCore.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "admire": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem admire_full_pipeline :
    admire.toVerbCore.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "envy": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem envy_full_pipeline :
    envy.toVerbCore.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "respect": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem respect_full_pipeline :
    respect.toVerbCore.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "value": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem value_full_pipeline :
    value.toVerbCore.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    LicensingPipeline.isLicensed Boundedness.open_ = false ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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

-- ════════════════════════════════════════════════════
-- § 5. Auto-Tests (loop over allVerbs)
-- ════════════════════════════════════════════════════

/-! These tests loop over `allVerbs` so adding a new verb to the fragment
    automatically includes it in the test suite — no per-verb theorem needed.
    If a new verb has an inconsistent annotation, `native_decide` fails. -/

/-- Pipeline consistency: for any verb with a vendlerClass annotation,
    the VendlerClass → Telicity → MereoTag → Boundedness chain must
    produce a licensing prediction that agrees with the for/in diagnostic.
    Returns `true` for verbs without vendlerClass (vacuously OK). -/
def pipelineOK (v : VerbEntry) : Bool :=
  match v.toVerbCore.vendlerClass with
  | none => true
  | some vc =>
    let tel := vc.telicity
    let mt := tel.toMereoTag
    let bnd := mt.toBoundedness
    let licensed := LicensingPipeline.isLicensed bnd
    -- Licensed verbs should accept "in X", blocked verbs "for X"
    if licensed then inXPrediction vc == .accept
    else forXPrediction vc == .accept

/-- Every verb in the fragment passes pipeline consistency. -/
theorem all_verbs_pipeline_ok :
    allVerbs.all pipelineOK = true := by native_decide

/-- VendlerClass × VerbIncClass coherence: sinc/inc verbs must be
    accomplishments (telic), cumOnly verbs must be activities (atelic).
    Returns `true` for verbs without verbIncClass (vacuously OK). -/
def incClassCoherent (v : VerbEntry) : Bool :=
  match v.toVerbCore.verbIncClass, v.toVerbCore.vendlerClass with
  | some .sinc, some vc => vc.telicity == .telic
  | some .inc, some vc => vc.telicity == .telic
  | some .cumOnly, some vc => vc.telicity == .atelic
  | _, _ => true

/-- Every verb in the fragment has coherent VendlerClass × VerbIncClass. -/
theorem all_verbs_inc_coherent :
    allVerbs.all incClassCoherent = true := by native_decide

/-- GRAD × SSR complementarity: no verb should predict both gradual
    change (sinc/inc) and subinterval reference (state/activity).
    Returns `true` if the verb doesn't predict both. -/
def gradSSRComplementary (v : VerbEntry) : Bool :=
  !(predictsGRAD v.toVerbCore.verbIncClass &&
    predictsSSR v.toVerbCore.vendlerClass)

/-- No verb in the fragment predicts both GRAD and SSR. -/
theorem all_verbs_grad_ssr_complementary :
    allVerbs.all gradSSRComplementary = true := by native_decide

/-- Count of verbs with vendlerClass annotations (for coverage tracking).
    Bump this number when adding new vendlerClass annotations. -/
theorem vendler_coverage_count :
    (allVerbs.filter (λ v => v.toVerbCore.vendlerClass.isSome)).length = 183 := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 6. Degree Achievement VendlerClass Consistency
-- ════════════════════════════════════════════════════

/-! Every verb with a degreeAchievementScale also has a vendlerClass, and
    the derived vendlerClass from the scale matches the stipulated one.
    Adding a new degree achievement verb with inconsistent annotations
    will cause `native_decide` to fail. -/

/-- For a verb with degreeAchievementScale, check that vendlerClass is
    present and matches the derived value from the scale. -/
def daVendlerConsistent (v : VerbEntry) : Bool :=
  match v.toVerbCore.degreeAchievementScale, v.toVerbCore.vendlerClass with
  | some das, some vc => das.defaultVendlerClass == vc
  | some _, none => false  -- DA scale present but no vendlerClass
  | none, _ => true        -- No DA scale, vacuously OK

/-- Every verb with degreeAchievementScale has vendlerClass matching
    the derived value. -/
theorem all_verbs_da_vendler_consistent :
    allVerbs.all daVendlerConsistent = true := by native_decide

end Phenomena.TenseAspect.Studies.AspectualConsistency
