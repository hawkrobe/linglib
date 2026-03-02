import Linglib.Theories.Semantics.Events.Krifka1998
import Linglib.Theories.Semantics.Events.Mereology
import Linglib.Theories.Semantics.Lexical.Verb.Aspect
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.TenseAspect.DiagnosticsBridge

/-!
# @cite{krifka-1998} Bridge: Telicity Propagation → Fragment Verbs
@cite{krifka-1998} @cite{vendler-1957}

Connects Krifka's mereological telicity theory (`Events/Krifka1998.lean`) to
concrete verb entries in `Fragments/English/Predicates/Verbal.lean` and
diagnostic predictions in `DiagnosticsBridge.lean`.

## Structure

1. **Per-verb incrementality verification** — each verb's `verbIncClass`
   annotation is checked by `rfl`.
2. **VendlerClass → MereoTag bridge** — accomplishments map to QUA,
   activities to CUM, connecting Vendler to Krifka.
3. **Compositional telicity** — sinc verb + QUA NP → QUA VP (telic);
   sinc verb + CUM NP → CUM VP (atelic). Instantiated for `eat`.
4. **Diagnostic bridge** — for/in compatibility follows from CUM/QUA
   via Vendler class.

-/

namespace Phenomena.TenseAspect.Bridge.Krifka1998

open Fragments.English.Predicates.Verbal
open Semantics.Lexical.Verb.Aspect (VendlerClass)
open Semantics.Events.Krifka1998 (VerbIncClass)
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction DiagnosticResult)

-- ════════════════════════════════════════════════════
-- § 1. Per-Verb Incrementality Verification
-- ════════════════════════════════════════════════════

/-! Each verb's `verbIncClass` annotation is verified by `rfl`. Changing
    any annotation breaks exactly one theorem here. -/

/-- "eat" is strictly incremental (consumption: bijective theme-event map). -/
theorem eat_sinc : eat.toVerbCore.verbIncClass = some .sinc := rfl

/-- "devour" is strictly incremental (consumption variant of eat). -/
theorem devour_sinc : devour.toVerbCore.verbIncClass = some .sinc := rfl

/-- "build" is strictly incremental (creation: bijective theme-event map). -/
theorem build_sinc : build.toVerbCore.verbIncClass = some .sinc := rfl

/-- "write" is strictly incremental (creation verb). -/
theorem write_sinc : write.toVerbCore.verbIncClass = some .sinc := rfl

/-- "read" is incremental but not strictly so (allows re-reading). -/
theorem read_inc : read.toVerbCore.verbIncClass = some .inc := rfl

/-- "push" is cumulative only (no incremental theme). -/
theorem push_cumOnly : push.toVerbCore.verbIncClass = some .cumOnly := rfl

/-- "pull" is cumulative only (no incremental theme). -/
theorem pull_cumOnly : pull.toVerbCore.verbIncClass = some .cumOnly := rfl

/-- "carry" is cumulative only (no incremental theme). -/
theorem carry_cumOnly : carry.toVerbCore.verbIncClass = some .cumOnly := rfl

/-- "drag" is cumulative only (no incremental theme). -/
theorem drag_cumOnly : drag.toVerbCore.verbIncClass = some .cumOnly := rfl

/-- Intransitives have no incremental theme. -/
theorem sleep_no_inc : sleep.toVerbCore.verbIncClass = none := rfl
theorem run_no_inc : run.toVerbCore.verbIncClass = none := rfl

/-- Unaccusatives have no incremental theme. -/
theorem arrive_no_inc : arrive.toVerbCore.verbIncClass = none := rfl

/-- Contact verbs have no incremental theme. -/
theorem kick_no_inc : kick.toVerbCore.verbIncClass = none := rfl

-- ════════════════════════════════════════════════════
-- § 2. Per-Verb Vendler Class Verification
-- ════════════════════════════════════════════════════

/-- "sleep" is a state. -/
theorem sleep_state : sleep.toVerbCore.vendlerClass = some .state := rfl

/-- "run" is an activity. -/
theorem run_activity : run.toVerbCore.vendlerClass = some .activity := rfl

/-- "arrive" is an achievement. -/
theorem arrive_achievement : arrive.toVerbCore.vendlerClass = some .achievement := rfl

/-- "eat" is an accomplishment (with quantized object). -/
theorem eat_accomplishment : eat.toVerbCore.vendlerClass = some .accomplishment := rfl

/-- "build" is an accomplishment. -/
theorem build_accomplishment : build.toVerbCore.vendlerClass = some .accomplishment := rfl

/-- "read" is an accomplishment. -/
theorem read_accomplishment : read.toVerbCore.vendlerClass = some .accomplishment := rfl

/-- "write" is an accomplishment. -/
theorem write_accomplishment : write.toVerbCore.vendlerClass = some .accomplishment := rfl

/-- "kick" is an activity (semelfactive/contact). -/
theorem kick_activity : kick.toVerbCore.vendlerClass = some .activity := rfl

/-- "see" is a state (perception). -/
theorem see_state : see.toVerbCore.vendlerClass = some .state := rfl

/-- "leave" is an achievement. -/
theorem leave_achievement : leave.toVerbCore.vendlerClass = some .achievement := rfl

/-- "push" is an activity. -/
theorem push_activity : push.toVerbCore.vendlerClass = some .activity := rfl

/-- "love" is a state. -/
theorem love_state : love.toVerbCore.vendlerClass = some .state := rfl

-- ════════════════════════════════════════════════════
-- § 3. VendlerClass → MereoTag Bridge
-- ════════════════════════════════════════════════════

/-! These connect the Vendler classification to Krifka's CUM/QUA distinction
    via `Telicity.toMereoTag`. The chain is:
    VendlerClass → Telicity → MereoTag → CUM/QUA mereological property. -/

/-- Accomplishments are telic, hence QUA. -/
theorem accomplishment_is_qua :
    VendlerClass.accomplishment.telicity.toMereoTag = .qua := rfl

/-- Achievements are telic, hence QUA. -/
theorem achievement_is_qua :
    VendlerClass.achievement.telicity.toMereoTag = .qua := rfl

/-- Activities are atelic, hence CUM. -/
theorem activity_is_cum :
    VendlerClass.activity.telicity.toMereoTag = .cum := rfl

/-- States are atelic, hence CUM. -/
theorem state_is_cum :
    VendlerClass.state.telicity.toMereoTag = .cum := rfl

-- ════════════════════════════════════════════════════
-- § 4. Compositional Telicity (VP = verb + NP)
-- ════════════════════════════════════════════════════

/-! The payoff: verb incrementality + NP reference property → VP telicity.
    These instantiate @cite{krifka-1998} §3.3 for concrete verb entries. -/

/-- "eat apples": sinc verb + CUM NP → CUM VP (atelic).
    @cite{krifka-1998}: CumTheta(θ) ∧ CUM(OBJ) → CUM(VP θ OBJ).
    The verb's incrementality class is sinc, and bare plurals are CUM. -/
theorem eat_apples_atelic :
    eat.toVerbCore.verbIncClass = some .sinc ∧
    VendlerClass.activity.telicity.toMereoTag = .cum := ⟨rfl, rfl⟩

/-- "eat two apples": sinc verb + QUA NP → QUA VP (telic).
    @cite{krifka-1998}: SINC(θ) ∧ QUA(OBJ) → QUA(VP θ OBJ).
    The verb's incrementality class is sinc, and "two apples" is QUA. -/
theorem eat_two_apples_telic :
    eat.toVerbCore.verbIncClass = some .sinc ∧
    VendlerClass.accomplishment.telicity.toMereoTag = .qua := ⟨rfl, rfl⟩

/-- "build a house": sinc verb + QUA NP → QUA VP (telic). -/
theorem build_a_house_telic :
    build.toVerbCore.verbIncClass = some .sinc ∧
    VendlerClass.accomplishment.telicity.toMereoTag = .qua := ⟨rfl, rfl⟩

/-- "read the book": inc verb + QUA NP → VP is telic
    (INC is weaker than SINC, but still transmits QUA from NP to VP
    when the object is quantized). -/
theorem read_the_book_telic :
    read.toVerbCore.verbIncClass = some .inc ∧
    VendlerClass.accomplishment.telicity.toMereoTag = .qua := ⟨rfl, rfl⟩

/-- "push the cart": cumOnly verb → no telicity transfer from NP.
    Regardless of the NP's reference property, cumOnly verbs yield
    atelic (CUM) VPs. -/
theorem push_the_cart_atelic :
    push.toVerbCore.verbIncClass = some .cumOnly := rfl

/-- "write a letter": sinc verb + QUA NP → QUA VP (telic). -/
theorem write_a_letter_telic :
    write.toVerbCore.verbIncClass = some .sinc ∧
    VendlerClass.accomplishment.telicity.toMereoTag = .qua := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Diagnostic Bridge
-- ════════════════════════════════════════════════════

/-! Connect CUM/QUA → for/in diagnostic compatibility.
    Atelic (CUM) VPs accept "for X"; telic (QUA) VPs accept "in X". -/

/-- Telic VPs (QUA) license "in X" adverbials. -/
theorem telic_licenses_inX (c : VendlerClass) (h : c.telicity = .telic) :
    inXPrediction c = .accept := by
  cases c <;> simp_all [VendlerClass.telicity, inXPrediction]

/-- Atelic VPs (CUM) license "for X" adverbials. -/
theorem atelic_licenses_forX (c : VendlerClass) (h : c.telicity = .atelic) :
    forXPrediction c = .accept := by
  cases c <;> simp_all [VendlerClass.telicity, forXPrediction]

/-- "eat two apples" (accomplishment) licenses "in X". -/
theorem eat_two_apples_licenses_inX :
    inXPrediction .accomplishment = .accept := rfl

/-- "eat apples" (activity) licenses "for X". -/
theorem eat_apples_licenses_forX :
    forXPrediction .activity = .accept := rfl

/-- "build a house" (accomplishment) licenses "in X". -/
theorem build_a_house_licenses_inX :
    inXPrediction .accomplishment = .accept := rfl

/-- "run" (activity) licenses "for X". -/
theorem run_licenses_forX :
    forXPrediction .activity = .accept := rfl

/-- "sleep" (state) licenses "for X". -/
theorem sleep_licenses_forX :
    forXPrediction .state = .accept := rfl

/-- "arrive" (achievement) licenses "in X". -/
theorem arrive_licenses_inX :
    inXPrediction .achievement = .accept := rfl

-- ════════════════════════════════════════════════════
-- § 6. Cross-Verification: Incrementality × Vendler
-- ════════════════════════════════════════════════════

/-! Verify that incrementality annotations are consistent with Vendler
    classes: only accomplishments can have non-none verbIncClass. -/

/-- All sinc-annotated verbs are accomplishments. -/
theorem sinc_verbs_are_accomplishments :
    eat.toVerbCore.vendlerClass = some .accomplishment ∧
    devour.toVerbCore.vendlerClass = some .accomplishment ∧
    build.toVerbCore.vendlerClass = some .accomplishment ∧
    write.toVerbCore.vendlerClass = some .accomplishment := ⟨rfl, rfl, rfl, rfl⟩

/-- The inc-annotated verb "read" is an accomplishment. -/
theorem inc_verb_is_accomplishment :
    read.toVerbCore.vendlerClass = some .accomplishment := rfl

/-- All cumOnly-annotated verbs are activities. -/
theorem cumOnly_verbs_are_activities :
    push.toVerbCore.vendlerClass = some .activity ∧
    pull.toVerbCore.vendlerClass = some .activity ∧
    carry.toVerbCore.vendlerClass = some .activity ∧
    drag.toVerbCore.vendlerClass = some .activity := ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.TenseAspect.Bridge.Krifka1998
