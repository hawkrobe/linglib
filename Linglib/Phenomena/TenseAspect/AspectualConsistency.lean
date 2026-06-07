import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Semantics.Spatial.Trace
import Linglib.Semantics.Lexical.LevinClass
import Linglib.Semantics.Aspect.Cumulativity
import Linglib.Semantics.Aspect.DegreeAchievement
import Linglib.Phenomena.TenseAspect.Diagnostics
import Linglib.Studies.Krifka1989
import Linglib.Studies.Krifka1998
import Linglib.Studies.Champollion2017

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

namespace AspectualConsistency

open Semantics.Lexical
open Features
open English.Predicates.Verbal
open Semantics.Aspect.Incremental (VerbIncClass)
open Core.Order (LicensingPipeline Boundedness MereoTag)
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction)
open Krifka1998 (predictsGRAD)
open Champollion2017 (predictsSSR)
open Semantics.Spatial.Path (PathShape)
open Features.DegreeAchievement (DegreeAchievementScale)

-- ════════════════════════════════════════════════════
-- § 1. VendlerClass × VerbIncClass Consistency
-- ════════════════════════════════════════════════════

/-! Sinc/inc verbs should be accomplishments (telic with incremental theme).
    CumOnly verbs should be activities (atelic, no theme-event mapping).
    Intransitives (no verbIncClass) can be any class. -/

/-- "eat": accomplishment + sinc → telic VP with incremental theme. -/
theorem eat_vendler_inc_consistent :
    eat.toVerb.vendlerClass = some .accomplishment ∧
    eat.toVerb.verbIncClass = some .sinc ∧
    VendlerClass.accomplishment.telicity = .telic := ⟨rfl, rfl, rfl⟩

/-- "build": accomplishment + sinc → telic VP with incremental theme. -/
theorem build_vendler_inc_consistent :
    build.toVerb.vendlerClass = some .accomplishment ∧
    build.toVerb.verbIncClass = some .sinc ∧
    VendlerClass.accomplishment.telicity = .telic := ⟨rfl, rfl, rfl⟩

/-- "read": accomplishment + inc → telic VP with incremental (non-strict) theme. -/
theorem read_vendler_inc_consistent :
    read.toVerb.vendlerClass = some .accomplishment ∧
    read.toVerb.verbIncClass = some .inc ∧
    VendlerClass.accomplishment.telicity = .telic := ⟨rfl, rfl, rfl⟩

/-- "push": activity + cumOnly → atelic VP, no theme-event mapping. -/
theorem push_vendler_inc_consistent :
    push.toVerb.vendlerClass = some .activity ∧
    push.toVerb.verbIncClass = some .cumOnly ∧
    VendlerClass.activity.telicity = .atelic := ⟨rfl, rfl, rfl⟩

/-- "kick": activity + no verbIncClass → atelic, no incremental theme. -/
theorem kick_vendler_inc_consistent :
    kick.toVerb.vendlerClass = some .activity ∧
    kick.toVerb.verbIncClass = none ∧
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
    predictsGRAD eat.toVerb.verbIncClass = true ∧
    predictsSSR eat.toVerb.vendlerClass = false := ⟨rfl, rfl⟩

/-- "build": GRAD ✓, SSR ✗ (accomplishment, sinc). -/
theorem build_grad_ssr_complementary :
    predictsGRAD build.toVerb.verbIncClass = true ∧
    predictsSSR build.toVerb.vendlerClass = false := ⟨rfl, rfl⟩

/-- "read": GRAD ✓, SSR ✗ (accomplishment, inc). -/
theorem read_grad_ssr_complementary :
    predictsGRAD read.toVerb.verbIncClass = true ∧
    predictsSSR read.toVerb.vendlerClass = false := ⟨rfl, rfl⟩

/-- "push": GRAD ✗, SSR ✓ (activity, cumOnly). -/
theorem push_grad_ssr_complementary :
    predictsGRAD push.toVerb.verbIncClass = false ∧
    predictsSSR push.toVerb.vendlerClass = true := ⟨rfl, rfl⟩

/-- "sleep": GRAD ✗, SSR ✓ (state, no incremental theme). -/
theorem sleep_grad_ssr_complementary :
    predictsGRAD sleep.toVerb.verbIncClass = false ∧
    predictsSSR sleep.toVerb.vendlerClass = true := ⟨rfl, rfl⟩

/-- "run": GRAD ✗, SSR ✓ (activity, no incremental theme). -/
theorem run_grad_ssr_complementary :
    predictsGRAD run.toVerb.verbIncClass = false ∧
    predictsSSR run.toVerb.vendlerClass = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Full Licensing Pipeline Convergence Per Verb
-- ════════════════════════════════════════════════════

/-! For each shared verb, verify the complete chain from fragment
    annotation through all classification levels to licensing and
    diagnostic predictions. Changing any fragment field breaks the
    entire chain for that verb. -/

/-- "eat": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem eat_full_pipeline :
    eat.toVerb.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "arrive": achievement → telic → QUA → closed → licensed → "in X" ✓. -/
theorem arrive_full_pipeline :
    arrive.toVerb.vendlerClass = some .achievement ∧
    VendlerClass.achievement.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "sleep": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem sleep_full_pipeline :
    sleep.toVerb.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "run": activity → atelic → CUM → open → blocked → "for X" ✓. -/
theorem run_full_pipeline :
    run.toVerb.vendlerClass = some .activity ∧
    VendlerClass.activity.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "see": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem see_full_pipeline :
    see.toVerb.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "leave": achievement → telic → QUA → closed → licensed → "in X" ✓. -/
theorem leave_full_pipeline :
    leave.toVerb.vendlerClass = some .achievement ∧
    VendlerClass.achievement.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "kill": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem kill_full_pipeline :
    kill.toVerb.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

-- Accomplishment verbs (telic, "in X")

/-- "give": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem give_full_pipeline :
    give.toVerb.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "cover": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem cover_full_pipeline :
    cover.toVerb.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "buy": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem buy_full_pipeline :
    buy.toVerb.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "sell": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem sell_full_pipeline :
    sell.toVerb.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "break": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem break_full_pipeline :
    break_.toVerb.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "tear": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem tear_full_pipeline :
    tear_.toVerb.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "burn": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem burn_full_pipeline :
    burn.toVerb.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "destroy": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem destroy_full_pipeline :
    destroy.toVerb.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "melt": accomplishment → telic → QUA → closed → licensed → "in X" ✓. -/
theorem melt_full_pipeline :
    melt.toVerb.vendlerClass = some .accomplishment ∧
    VendlerClass.accomplishment.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

-- Achievement verbs (telic, "in X")

/-- "put": achievement → telic → QUA → closed → licensed → "in X" ✓. -/
theorem put_full_pipeline :
    put.toVerb.vendlerClass = some .achievement ∧
    VendlerClass.achievement.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "meet": achievement → telic → QUA → closed → licensed → "in X" ✓. -/
theorem meet_full_pipeline :
    meet.toVerb.vendlerClass = some .achievement ∧
    VendlerClass.achievement.telicity = .telic ∧
    Telicity.telic.toMereoTag = .qua ∧
    MereoTag.qua.toBoundedness = .closed ∧
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

-- Activity verbs (atelic, "for X")

/-- "chase": activity → atelic → CUM → open → blocked → "for X" ✓. -/
theorem chase_full_pipeline :
    chase.toVerb.vendlerClass = some .activity ∧
    VendlerClass.activity.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "hit": activity → atelic → CUM → open → blocked → "for X" ✓. -/
theorem hit_full_pipeline :
    hit.toVerb.vendlerClass = some .activity ∧
    VendlerClass.activity.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

-- State verbs (atelic, "for X")

/-- "weigh": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem weigh_full_pipeline :
    weigh.toVerb.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "measure": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem measure_full_pipeline :
    measure.toVerb.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "enjoy": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem enjoy_full_pipeline :
    enjoy.toVerb.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "like": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem like_full_pipeline :
    like.toVerb.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "hate": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem hate_full_pipeline :
    hate.toVerb.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "admire": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem admire_full_pipeline :
    admire.toVerb.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "envy": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem envy_full_pipeline :
    envy.toVerb.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "respect": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem respect_full_pipeline :
    respect.toVerb.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-- "value": state → atelic → CUM → open → blocked → "for X" ✓. -/
theorem value_full_pipeline :
    value.toVerb.vendlerClass = some .state ∧
    VendlerClass.state.telicity = .atelic ∧
    Telicity.atelic.toMereoTag = .cum ∧
    MereoTag.cum.toBoundedness = .open_ ∧
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    forXPrediction .state = .accept := ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Motion Verb Cross-Classification
-- ════════════════════════════════════════════════════

/-! Motion verbs have both vendlerClass and levinClass annotations.
    Verify these are consistent: inherently-directed-motion verbs
    (achievements) have bounded paths, manner-of-motion verbs
    (activities) have no inherent path. -/

/-- "arrive": achievement + inherentlyDirectedMotion + bounded path. -/
theorem arrive_motion_consistent :
    arrive.toVerb.vendlerClass = some .achievement ∧
    arrive.toVerb.levinClass = some .inherentlyDirectedMotion ∧
    LevinClass.inherentlyDirectedMotion.pathSpec = some .bounded := ⟨rfl, rfl, rfl⟩

/-- "leave": achievement + leave class + source path. -/
theorem leave_motion_consistent :
    leave.toVerb.vendlerClass = some .achievement ∧
    leave.toVerb.levinClass = some .leave ∧
    LevinClass.leave.pathSpec = some .source := ⟨rfl, rfl, rfl⟩

/-- "run": activity + mannerOfMotion + no inherent path. -/
theorem run_motion_consistent :
    run.toVerb.vendlerClass = some .activity ∧
    run.toVerb.levinClass = some .mannerOfMotion ∧
    LevinClass.mannerOfMotion.pathSpec = none := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Auto-Tests (loop over allVerbs)
-- ════════════════════════════════════════════════════

/-! These tests loop over `allVerbs` so adding a new verb to the fragment
    automatically includes it in the test suite — no per-verb theorem needed.
    If a new verb has an inconsistent annotation, the decision-procedure
    checks fail. -/

/-- Pipeline consistency: for any verb with a vendlerClass annotation,
    the VendlerClass → Telicity → MereoTag → Boundedness chain must
    produce a licensing prediction that agrees with the for/in diagnostic.
    Vacuously OK for verbs without vendlerClass. Licensed (telic) verbs
    accept "in X"; blocked (atelic) verbs accept or are coerced with
    "for X" (semelfactives are coerced). -/
def PipelineOK (v : VerbEntry) : Prop :=
  match v.toVerb.vendlerClass with
  | none => True
  | some vc =>
    (LicensingPipeline.IsLicensed vc.telicity.toMereoTag.toBoundedness ∧
      inXPrediction vc = .accept) ∨
    (¬ LicensingPipeline.IsLicensed vc.telicity.toMereoTag.toBoundedness ∧
      (forXPrediction vc = .accept ∨ forXPrediction vc = .coerced))

instance (v : VerbEntry) : Decidable (PipelineOK v) := by
  unfold PipelineOK
  split <;> infer_instance

set_option maxRecDepth 2048 in
/-- Every verb in the fragment passes pipeline consistency. -/
theorem all_verbs_pipeline_ok : ∀ v ∈ allVerbs, PipelineOK v := by decide

/-- VendlerClass × VerbIncClass coherence: sinc/inc verbs must be
    accomplishments (telic), cumOnly verbs must be activities (atelic).
    Returns `true` for verbs without verbIncClass (vacuously OK). -/
def incClassCoherent (v : VerbEntry) : Bool :=
  match v.toVerb.verbIncClass, v.toVerb.vendlerClass with
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
  !(predictsGRAD v.toVerb.verbIncClass &&
    predictsSSR v.toVerb.vendlerClass)

/-- No verb in the fragment predicts both GRAD and SSR. -/
theorem all_verbs_grad_ssr_complementary :
    allVerbs.all gradSSRComplementary = true := by native_decide

/-- Count of verbs with vendlerClass annotations (for coverage tracking).
    Bump this number when adding new vendlerClass annotations. -/
theorem vendler_coverage_count :
    (allVerbs.filter (λ v => v.toVerb.vendlerClass.isSome)).length = 237 := by
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
  match v.toVerb.degreeAchievementScale, v.toVerb.vendlerClass with
  | some das, some vc => das.defaultVendlerClass == vc
  | some _, none => false  -- DA scale present but no vendlerClass
  | none, _ => true        -- No DA scale, vacuously OK

/-- Every verb with degreeAchievementScale has vendlerClass matching
    the derived value. -/
theorem all_verbs_da_vendler_consistent :
    allVerbs.all daVendlerConsistent = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. K89 Table 14 ↔ K98 VerbIncClass ↔ Fragment
-- ════════════════════════════════════════════════════

/-! K89's table-14 thematic classes (gradualEffectedPatient /
    gradualConsumedPatient / gradualPatient / affectedPatient /
    stimulus) refine to K98's `VerbIncClass` (sinc / inc / cumOnly)
    via `Krifka1989.K89ThematicClass.toVerbIncClass`. The fragment
    annotations in `Verbal.lean` should be consistent with both: e.g.,
    `eat`'s K98 verbIncClass = sinc must match K89's eat-an-apple class
    (gradualConsumedPatient → toVerbIncClass = sinc). This section
    makes the three-layer K89 ↔ K98 ↔ Fragment chain explicit. -/

/-- *eat an apple* (K89 §4 gradual-consumed-patient) refines to K98 sinc,
    which matches `eat`'s fragment annotation. -/
theorem k89_eat_refines_k98_matches_fragment :
    Krifka1989.eatAnApple.thematicClass.toVerbIncClass = .sinc ∧
    eat.toVerb.verbIncClass = some .sinc := ⟨rfl, rfl⟩

/-- *write a letter* (K89 §4 gradual-effected-patient) refines to K98 sinc,
    which matches `write`'s fragment annotation. -/
theorem k89_write_refines_k98_matches_fragment :
    Krifka1989.writeALetter.thematicClass.toVerbIncClass = .sinc ∧
    write.toVerb.verbIncClass = some .sinc := ⟨rfl, rfl⟩

/-- *read a letter* (K89 §4 gradual-patient, lacks UNI-E) refines to
    K98 inc, which matches `read`'s fragment annotation (allows
    re-reading). -/
theorem k89_read_refines_k98_matches_fragment :
    Krifka1989.readALetter.thematicClass.toVerbIncClass = .inc ∧
    read.toVerb.verbIncClass = some .inc := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 8. Propositional Propagation Tests (Typeclass Form)
-- ════════════════════════════════════════════════════

/-! Sections 1–7 verify the Bool-tag pipeline (VendlerClass → Telicity
    → MereoTag → Boundedness → for/in licensing). This section
    verifies the **propositional** propagation chain at the typeclass
    level: given `[IsSincVerb θ]` (which bundles SINC + UP + CumTheta;
    declared in `Semantics/Events/Aspect/Incremental.lean`),
    QUA and CUM propagate through the verb's incremental theme to the
    VP via substrate's typeclass-form `qua_propagation` and
    `cum_propagation` (`Semantics/Events/Aspect/Cumulativity.lean`).

    These are propositional cousins of §3's full-pipeline tests — same
    K89 → K98 chain, but at the substrate level rather than the
    Bool-tag level. They fire on any `[IsSincVerb θ]` instance; the
    concrete `eatThemeToy` instance in
    `Studies/Krifka1998.lean` §9 proves the
    typeclass admits real witnesses. -/

section PropositionalConsistency

open Semantics.ArgumentStructure (UP CumTheta IsCumThetaVerb)
open Semantics.Aspect.Incremental (SINC IsSincVerb)
open Semantics.Aspect.Cumulativity
  (VP cum_propagation qua_propagation)
open Mereology (CUM QUA)

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- For any sinc verb θ and any QUA object, the VP is QUA (telic).
    Verifies the K89 → K98 propositional chain at the typeclass level:
    given `[IsSincVerb θ]` (bundling SINC + UP + CumTheta), QUA
    propagates through the verb's incremental theme to the VP. Direct
    invocation of substrate's typeclass-form `qua_propagation`. -/
theorem sinc_verb_qua_object_yields_qua_vp
    (θ : α → β → Prop) [IsSincVerb θ]
    {OBJ : α → Prop} (hQua : QUA OBJ) :
    QUA (VP θ OBJ) :=
  qua_propagation hQua

/-- For any verb θ with CumTheta — including cumOnly classes
    (*push*, *carry*) and the strictly stronger SINC/INC classes
    (which auto-derive `[IsCumThetaVerb θ]` via the upward instances
    in `Aspect/Incremental.lean` / `Aspect/Incremental.lean`) —
    a CUM object yields a CUM VP. K98 §3.3 cum-propagation at maximal
    typeclass generality; subsumes the SINC-only case. Direct
    invocation of substrate's typeclass-form `cum_propagation`. -/
theorem cum_theta_verb_cum_object_yields_cum_vp
    (θ : α → β → Prop) [IsCumThetaVerb θ]
    {OBJ : α → Prop} (hCum : CUM OBJ) :
    CUM (VP θ OBJ) :=
  cum_propagation hCum

end PropositionalConsistency

end AspectualConsistency
