import Linglib.Semantics.ArgumentStructure.Properties
import Linglib.Semantics.Aspect.Incremental
import Linglib.Semantics.Aspect.Cumulativity
import Linglib.Semantics.Events.CEM
import Linglib.Semantics.Spatial.Trace
import Linglib.Semantics.Lexical.LevinClass
import Linglib.Semantics.Events.Adjacency
import Linglib.Semantics.Aspect.PrecedenceClosure
import Linglib.Features.Aktionsart
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.TenseAspect.Diagnostics
import Linglib.Studies.Krifka1989
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic

/-!
# [krifka-1998] *The Origins of Telicity*

K98's two distinctive contributions, formalized end-to-end:

* **Part I — §3 Incrementality** (CUM/QUA propagation through SINC/INC
  verbs; Vendler classification; for/in diagnostics).
* **Part II — §4 Movement** (path/movement extension of mereological
  telicity: a movement event is telic iff its path is bounded; EXP /
  SEINC / ADJ / SMR / MovementClosure / MR propositional substrate).

The substrate predicates (SUM, UO, UE, MO, MSO, MSE, GUE, SINC, INC,
CumTheta — K98 §3.2 eq. 43-52, eq. 59) live in
`Semantics/Events/{Incrementality,ThematicRoleProperties}.lean`;
the σ-trace pullback machinery in `Semantics/Spatial/Trace.lean`.
This file exercises both on the English fragment and inlines the §4
movement-relation predicates (formerly in
`Semantics/Events/MovementRelations.lean`).

## Main definitions

Part I (§3 incrementality):

* Per-verb `*_sinc` / `*_inc` / `*_cumOnly` tripwire theorems
* VendlerClass → MereoTag bridge via `Telicity.toMereoTag`
* `eat_two_apples_qua_propositional` / `eat_apples_cum_propositional` —
  K98 §3.3 propagation invoked on abstract θ
* `IsSincVerb (eatThemeToy)` instance + applied propagation theorems
  (the constructive witness that the typeclass admits non-axiomatic
  realizations)
* K89 ↔ K98 sister-paper refinement bridge (uses
  `K89ThematicClass.toVerbIncClass` from `Studies/Krifka1989.lean`)

Part II (§4 movement):

* `EXP` / `SEINC` / `ADJ` / `SMR` — K98 §4 propositional predicates
* `MovementClosure` / `MR` — K98 §4.3 closure substrate (TANG_H-free)
* `expEv` / `seincEv` / `smrPath` / `mrPath` — `Event Time` instantiations
* `MotionVPDatum` / `motionData` — Bool-tag-level VP data
* `walked_from_to_telic_propositional` /
  `walked_towards_atelic_propositional` — σ-pullback theorems backing
  the K98 §4.5 *walked from X to Y* / *walked towards X* analyses

## TODO

* **TEL substrate**: K98 §2.5 eq. 37 defines TEL strictly weaker than
  QUA. Linglib's `Telicity.toMereoTag .telic = .qua` collapse is an
  approximation; a faithful TEL would need INI/FIN initial/final-part
  predicates over events.
* **TANG_H tangentiality** (K98 eq. 17) on directed paths. Without it,
  `MR` admits telekinetic non-meeting concatenations (K98 eq. 70.c).
  Adding TANG_H requires a `DirectedPath` substrate not yet in linglib.
* **Cross-dimensional movements** (K98 §4.6: heat, bake, whip — eq. 76-77).
  Structurally identical to spatial movements; require the same
  `DirectedPath` generalization.
* **Full ADJ axioms** on adjacency (K98 §2.3 eq. 14.b). The concrete
  `Path.adjacent` + `Event.adjacent` satisfy them but the propositional
  theorems are not added.
* **`cumOnly` is the formaliser's term, not K98's.** K98 distinguishes
  verbs that are merely cumulative (CUM, eq. 44) without strict
  incrementality (¬SINC, ¬MSE). The `VerbIncClass.cumOnly` constructor
  name is anachronistic shorthand.

## What this file is NOT

* Not a critique of K98's classification — that's `Studies/Filip2012.lean`
  (three-way CUM / QUA / ¬CUM ∧ ¬QUA via K98 §3.3 propagation).
* Not a fragment-only verb-annotation file — fragment annotations in
  `Fragments/English/Predicates/Verbal.lean` are tested per-verb here
  as a tripwire layer.

## References

* [krifka-1998] (primary, both §3 and §4 covered)
* [krifka-1989] (sister paper: `Studies/Krifka1989.lean`)
* [vendler-1957] (Vendler classes used in Part I § 6)
* [filip-2012] (downstream critique: `Studies/Filip2012.lean`)
-/

namespace Krifka1998

open English.Predicates.Verbal
open Features
open Semantics.Lexical
open _root_.Mereology
open Semantics.ArgumentStructure (UP CumTheta IsCumThetaVerb)
open Semantics.Aspect.Incremental (SINC VerbIncClass IsSincVerb IsIncVerb)
open Semantics.Aspect.Cumulativity (VP cum_propagation qua_propagation)
open Semantics.Spatial (Trace)
open Semantics.Spatial.Trace (pathShapeToTelicity)
open Semantics.Spatial.Path (PathShape)
open Core.Order (LicensingPipeline)
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction DiagnosticResult)

/-! ### Per-Verb Incrementality Verification -/

/-! Each verb's `verbIncClass` annotation is verified by `rfl`. Changing
    any annotation breaks exactly one theorem here. These earn their
    place as fragment-annotation tripwires; mathlib would call them
    `example`s, but as `theorem`s they're discoverable via `#check`. -/

/-- "eat" is strictly incremental (consumption: bijective theme-event map). -/
theorem eat_sinc : eat.toVerb.verbIncClass = some .sinc := rfl

/-- "devour" is strictly incremental (consumption variant of eat). -/
theorem devour_sinc : devour.toVerb.verbIncClass = some .sinc := rfl

/-- "build" is strictly incremental (creation: bijective theme-event map). -/
theorem build_sinc : build.toVerb.verbIncClass = some .sinc := rfl

/-- "write" is strictly incremental (creation verb). -/
theorem write_sinc : write.toVerb.verbIncClass = some .sinc := rfl

/-- "read" is incremental but not strictly so (allows re-reading per K98 §3.6). -/
theorem read_inc : read.toVerb.verbIncClass = some .inc := rfl

/-- "push" is cumulative only (no incremental theme — the formaliser's
    "cumOnly" is shorthand; K98 calls it CUM-without-MSE/MSO). -/
theorem push_cumOnly : push.toVerb.verbIncClass = some .cumOnly := rfl

/-- "pull" is cumulative only. -/
theorem pull_cumOnly : pull.toVerb.verbIncClass = some .cumOnly := rfl

/-- "carry" is cumulative only. -/
theorem carry_cumOnly : carry.toVerb.verbIncClass = some .cumOnly := rfl

/-- "drag" is cumulative only. -/
theorem drag_cumOnly : drag.toVerb.verbIncClass = some .cumOnly := rfl

/-- Intransitives have no incremental theme. -/
theorem sleep_no_inc : sleep.toVerb.verbIncClass = none := rfl
theorem run_no_inc : run.toVerb.verbIncClass = none := rfl

/-- Unaccusatives have no incremental theme. -/
theorem arrive_no_inc : arrive.toVerb.verbIncClass = none := rfl

/-- Contact verbs have no incremental theme. -/
theorem kick_no_inc : kick.toVerb.verbIncClass = none := rfl

/-! ### Per-Verb Vendler Class Verification -/

/-- "sleep" is a state. -/
theorem sleep_state : sleep.toVerb.vendlerClass = some .state := rfl

/-- "run" is an activity. -/
theorem run_activity : run.toVerb.vendlerClass = some .activity := rfl

/-- "arrive" is an achievement. -/
theorem arrive_achievement : arrive.toVerb.vendlerClass = some .achievement := rfl

/-- "eat" is an accomplishment (with quantized object). -/
theorem eat_accomplishment : eat.toVerb.vendlerClass = some .accomplishment := rfl

/-- "build" is an accomplishment. -/
theorem build_accomplishment : build.toVerb.vendlerClass = some .accomplishment := rfl

/-- "read" is an accomplishment. -/
theorem read_accomplishment : read.toVerb.vendlerClass = some .accomplishment := rfl

/-- "write" is an accomplishment. -/
theorem write_accomplishment : write.toVerb.vendlerClass = some .accomplishment := rfl

/-- "kick" is an activity (semelfactive/contact). -/
theorem kick_activity : kick.toVerb.vendlerClass = some .activity := rfl

/-- "see" is a state (perception). -/
theorem see_state : see.toVerb.vendlerClass = some .state := rfl

/-- "leave" is an achievement. -/
theorem leave_achievement : leave.toVerb.vendlerClass = some .achievement := rfl

/-- "push" is an activity. -/
theorem push_activity : push.toVerb.vendlerClass = some .activity := rfl

/-- "love" is a state. -/
theorem love_state : love.toVerb.vendlerClass = some .state := rfl

/-! ### VendlerClass → MereoTag Bridge -/

/-! These connect the Vendler classification to K89's CUM/QUA distinction
    via `Telicity.toMereoTag`. The chain is:
    VendlerClass → Telicity → MereoTag → CUM/QUA mereological property.

    **Caveat: TEL ⊃ QUA in K98, but collapsed here.** K98 §2.5 (eq. 37,
    page 9) defines TEL_E (telicity) strictly weaker than QUA
    (quantization): every QUA predicate is TEL, but not every TEL
    predicate is QUA (K98 gives the run-time-3-4pm counterexample on
    page 9). The `Telicity.toMereoTag .telic = .qua` collapse used here
    is faithful for the typical Vendler-class accomplishments and
    achievements (which are both TEL and QUA), but a complete K98
    formalization would need a separate propositional `TEL` predicate
    distinct from `QUA`. Adding `def TEL` requires INI/FIN initial/final-
    part predicates over events, which linglib's K98 theory doesn't
    house — deferred. -/

/-- Accomplishments are telic, hence (under the TEL = QUA collapse) QUA. -/
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

/-! ### Compositional Telicity (VP = verb + NP) -/

/-! The payoff: verb incrementality + NP reference property → VP telicity.
    These instantiate K98 §3.3 (eq. 53-54) for concrete verb entries.

    Round-1 audit additions: propositional invocations of K98 theory's
    `cum_propagation` and `qua_propagation` on abstract θ instances
    (parallel to K89 study §3's `qmod_of_cum_is_qua` calls), making the
    Bool-tag conjunctions below into substrate-honest derivations
    rather than stipulated `⟨rfl, rfl⟩`. -/

/-- "eat apples": sinc verb + CUM NP → CUM VP (atelic).
    K98 §3.3: CumTheta(θ) ∧ CUM(OBJ) → CUM(VP θ OBJ).
    The verb's incrementality class is sinc, and bare plurals are CUM. -/
theorem eat_apples_atelic :
    eat.toVerb.verbIncClass = some .sinc ∧
    VendlerClass.activity.telicity.toMereoTag = .cum := ⟨rfl, rfl⟩

/-- "eat two apples": sinc verb + QUA NP → QUA VP (telic).
    K98 §3.3: SINC(θ) ∧ QUA(OBJ) → QUA(VP θ OBJ).
    The verb's incrementality class is sinc, and "two apples" is QUA. -/
theorem eat_two_apples_telic :
    eat.toVerb.verbIncClass = some .sinc ∧
    VendlerClass.accomplishment.telicity.toMereoTag = .qua := ⟨rfl, rfl⟩

/-- "build a house": sinc verb + QUA NP → QUA VP (telic). -/
theorem build_a_house_telic :
    build.toVerb.verbIncClass = some .sinc ∧
    VendlerClass.accomplishment.telicity.toMereoTag = .qua := ⟨rfl, rfl⟩

/-- "read the book": inc verb + QUA NP → VP is telic
    (INC is weaker than SINC, but still transmits QUA from NP to VP
    when the object is quantized, K98 §3.6). -/
theorem read_the_book_telic :
    read.toVerb.verbIncClass = some .inc ∧
    VendlerClass.accomplishment.telicity.toMereoTag = .qua := ⟨rfl, rfl⟩

/-- "push the cart": cumOnly verb → no telicity transfer from NP.
    Regardless of the NP's reference property, cumOnly verbs yield
    atelic (CUM) VPs. -/
theorem push_the_cart_atelic :
    push.toVerb.verbIncClass = some .cumOnly := rfl

/-- "write a letter": sinc verb + QUA NP → QUA VP (telic). -/
theorem write_a_letter_telic :
    write.toVerb.verbIncClass = some .sinc ∧
    VendlerClass.accomplishment.telicity.toMereoTag = .qua := ⟨rfl, rfl⟩

/-! ### §4.5 Propositional propagation invocations (typeclass form)

    The Bool-tag conjunctions above check fragment annotations and tag
    composition; the theorems below actually invoke K98 theory's
    `cum_propagation` and `qua_propagation` (typeclass-canonical
    forms) on abstract θ + OBJ instances. This is the same shape as
    K89 study §3's calls of `qmod_of_cum_is_qua` — making the
    substrate-bridge promise concrete rather than rhetorical. -/

section PropositionalPropagation

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- *eat apples* propositional: K98 §3.3 CUM propagation. Given any
    `[IsCumThetaVerb θ]` (eat's role — and any of the K98 verb classes
    via upward instances) and a CUM object (apples), VP is CUM. -/
theorem eat_apples_cum_propositional
    {θ : α → β → Prop} [IsCumThetaVerb θ]
    {Apples : α → Prop} (hApples : CUM Apples) :
    CUM (VP θ Apples) :=
  cum_propagation hApples

/-- *eat two apples* propositional: K98 §3.3 QUA propagation. Given
    `[IsSincVerb θ]` (eat's role, bundling SINC + UP) and a QUA
    object (two apples), VP is QUA. -/
theorem eat_two_apples_qua_propositional
    {θ : α → β → Prop} [IsSincVerb θ]
    {TwoApples : α → Prop} (hTwoApples : QUA TwoApples) :
    QUA (VP θ TwoApples) :=
  qua_propagation hTwoApples

end PropositionalPropagation

/-! ### Diagnostic Bridge -/

/-! Connect CUM/QUA → for/in diagnostic compatibility.
    Atelic (CUM) VPs accept "for X"; telic (QUA) VPs accept "in X".

    Round-1 audit deletions: 6 per-verb `inXPrediction .X = .accept := rfl`
    theorems removed — they were tautological restatements of the
    `Diagnostics.inXPrediction` definition (since `eat_two_apples_licenses_inX`
    and `build_a_house_licenses_inX` had identical statements, both
    passing `.accomplishment`, neither was about a specific verb). The
    general `telic_licenses_inX` and `durative_atelic_licenses_forX`
    below carry the diagnostic bridge work. -/

/-- Telic VPs (QUA) license "in X" adverbials. -/
theorem telic_licenses_inX (c : VendlerClass) (h : c.telicity = .telic) :
    inXPrediction c = .accept := by
  cases c <;> simp_all [VendlerClass.telicity, inXPrediction]

/-- Durative atelic VPs (CUM + durative) license "for X" adverbials.
    Semelfactives are atelic but punctual — "for X" coerces to iterative. -/
theorem durative_atelic_licenses_forX (c : VendlerClass)
    (h : c.telicity = .atelic) (hd : c.duration = .durative) :
    forXPrediction c = .accept := by
  cases c <;> simp_all [VendlerClass.telicity, VendlerClass.duration, forXPrediction]

/-! ### Cross-Verification: Incrementality × Vendler -/

/-! Verify that incrementality annotations are consistent with Vendler
    classes: only accomplishments can have non-none verbIncClass. -/

/-- All sinc-annotated verbs are accomplishments. -/
theorem sinc_verbs_are_accomplishments :
    eat.toVerb.vendlerClass = some .accomplishment ∧
    devour.toVerb.vendlerClass = some .accomplishment ∧
    build.toVerb.vendlerClass = some .accomplishment ∧
    write.toVerb.vendlerClass = some .accomplishment := ⟨rfl, rfl, rfl, rfl⟩

/-- The inc-annotated verb "read" is an accomplishment. -/
theorem inc_verb_is_accomplishment :
    read.toVerb.vendlerClass = some .accomplishment := rfl

/-- All cumOnly-annotated verbs are activities. -/
theorem cumOnly_verbs_are_activities :
    push.toVerb.vendlerClass = some .activity ∧
    pull.toVerb.vendlerClass = some .activity ∧
    carry.toVerb.vendlerClass = some .activity ∧
    drag.toVerb.vendlerClass = some .activity := ⟨rfl, rfl, rfl, rfl⟩

/-! ## Gradual Change (GRAD) Predictions -/

/-! Connects GRAD theory to concrete verb entries.

    Round-1 audit fixes: `GRADDatum.verb : String` and
    `GRADDatum.objectMeasure : String` were the round-2-K89 String-field
    anti-pattern recreated; replaced with `GRADVerb` enum +
    `GRADObjectMeasure` enum. `native_decide` on `all_grad_data_matches`
    eliminated by structurally lifting the verb match into the enum's
    `toIncClass` projection. -/

/-- Verbs covered by the GRAD-prediction data. -/
inductive GRADVerb where
  | eat | build | read | push | kick
  deriving DecidableEq, Repr

/-- English lemma for each GRAD verb. -/
def GRADVerb.lemma : GRADVerb → String
  | .eat => "eat"
  | .build => "build"
  | .read => "read"
  | .push => "push"
  | .kick => "kick"

/-- Each verb's expected `VerbIncClass` per K98. Defined as literal
    constructors so that `decide` can close `all_grad_data_matches`
    structurally; the fragment-annotation tripwire is the separate
    `gradVerb_matches_fragment` theorem below. -/
def GRADVerb.expectedIncClass : GRADVerb → Option VerbIncClass
  | .eat => some .sinc
  | .build => some .sinc
  | .read => some .inc
  | .push => some .cumOnly
  | .kick => none

/-- Tripwire: each `GRADVerb.expectedIncClass` matches the fragment's
    `verbIncClass` annotation. If a fragment annotation drifts, this
    theorem breaks per-verb (one conjunct per verb). The
    `expectedIncClass` literal is what `decide` consumes for
    `all_grad_data_matches`; this theorem keeps the literal in sync
    with the fragment. -/
theorem gradVerb_matches_fragment :
    GRADVerb.eat.expectedIncClass = eat.toVerb.verbIncClass ∧
    GRADVerb.build.expectedIncClass = build.toVerb.verbIncClass ∧
    GRADVerb.read.expectedIncClass = read.toVerb.verbIncClass ∧
    GRADVerb.push.expectedIncClass = push.toVerb.verbIncClass ∧
    GRADVerb.kick.expectedIncClass = kick.toVerb.verbIncClass :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The dimension along which a verb's GRAD measure operates. -/
inductive GRADObjectMeasure where
  | weightOrVolume    -- consumption verbs
  | proportionDone    -- creation verbs
  | pages             -- read
  | weight            -- push
  | force             -- kick (no GRAD)
  deriving DecidableEq, Repr

structure GRADDatum where
  verb : GRADVerb
  objectMeasure : GRADObjectMeasure
  expectsGRAD : Bool
  deriving Repr, DecidableEq

def eatGRAD : GRADDatum :=
  { verb := .eat, objectMeasure := .weightOrVolume, expectsGRAD := true }
def buildGRAD : GRADDatum :=
  { verb := .build, objectMeasure := .proportionDone, expectsGRAD := true }
def readGRAD : GRADDatum :=
  { verb := .read, objectMeasure := .pages, expectsGRAD := true }
def pushNoGRAD : GRADDatum :=
  { verb := .push, objectMeasure := .weight, expectsGRAD := false }
def kickNoGRAD : GRADDatum :=
  { verb := .kick, objectMeasure := .force, expectsGRAD := false }

def gradData : List GRADDatum :=
  [eatGRAD, buildGRAD, readGRAD, pushNoGRAD, kickNoGRAD]

/-- Whether a verb's incrementality class predicts GRAD.

    This is a Bool projection of K98 theory's propositional `GRAD`
    predicate; the
    propositional version is what `grad_of_sinc` proves. Keeping the
    Bool-tag projection here as a quick-check; consumers needing the
    propositional content should use `grad_of_sinc` directly on
    abstract θ instances. -/
def predictsGRAD : Option VerbIncClass → Bool
  | some .sinc => true
  | some .inc => true
  | some .cumOnly => false
  | none => false

-- Per-verb GRAD verification (fragment-tripwire)

theorem eat_predicts_grad :
    predictsGRAD eat.toVerb.verbIncClass = true := rfl
theorem build_predicts_grad :
    predictsGRAD build.toVerb.verbIncClass = true := rfl
theorem read_predicts_grad :
    predictsGRAD read.toVerb.verbIncClass = true := rfl
theorem push_no_grad :
    predictsGRAD push.toVerb.verbIncClass = false := rfl
theorem kick_no_grad :
    predictsGRAD kick.toVerb.verbIncClass = false := rfl

/-- All GRAD data matches the K98-expected verb classification. The
    `decide` closure works because `verb.expectedIncClass` is
    structurally reducible (literal-tag enum), unlike a fragment-
    projection that goes through `Verbal.lean`'s `VerbEntry`. The
    fragment-annotation tripwire is `gradVerb_matches_fragment`. -/
theorem all_grad_data_matches :
    gradData.all (fun d => predictsGRAD d.verb.expectedIncClass == d.expectsGRAD) = true := by
  decide

/-! ### K98 §3.5 Eq. 58: Mary ate peanuts in 0.43 seconds -/

/-! K98 §3.5 (page 18, eq. 58) introduces *Mary is an incredibly fast
    eater. Yesterday she ate peanuts in 0.43 seconds!* — K98's own
    version of K89 §5's *Ann drank wine in 0.43 sec*. K98 uses it to
    argue that **temporal atomicity** (not quantization) is what
    licenses *in*-X adverbials: "even though *eat peanuts* is not
    quantized, it can be understood as temporally atomic. One chewing
    move may be a part of an event of eating peanuts, but not yet an
    event of eating peanuts."

    The K89 study has an analogous ATM section (citing K89 T4); this
    file mirrors it for K98 §3.5. The substrate-witness theorem
    (showing a CUM-but-temporally-atomic predicate accepts *in*-X)
    requires event-CEM atom infrastructure beyond this file's scope;
    documented as data + linguistic motivation. -/

/-- The K98 §3.5 atomicity-vs-quantization argument has three structural
    parts: the object NP's mereological reference type, the VP's
    licensing condition for *in*-X, and the temporal-atomicity flag
    that licenses *in*-X even when QUA fails. Captured here as a
    structure with enum-typed fields (`MereoTag`, `DiagnosticResult`)
    rather than a triple of `Bool`s — Bool tags would be the round-2
    K89 anti-pattern. -/
structure K98AtomicityDatum where
  sentence : String
  objectNP : String
  /-- Object NP's mereo reference type per K98 §3.3 (CUM or QUA). -/
  objectRef : Core.Order.MereoTag
  /-- Diagnostic acceptance per K98 §3.4. -/
  inXAcceptance : DiagnosticResult
  deriving Repr

/-- *Mary ate peanuts in 0.43 seconds* (K98 §3.5 eq. 58). The peanuts
    NP is CUM (mass-bare-plural — bare plurals are CUM via algebraic
    closure, cf. K89 §3 / `Krifka1989.applesNP`). The bounded-duration
    eating predicate is temporally atomic — no sub-event of a 0.43-second
    peanut-eating is also a 0.43-second peanut-eating. K98 §3.5 argues
    this licenses *in*-X via temporal atomicity, not quantization. -/
def maryAtePeanutsIn043Sec : K98AtomicityDatum :=
  { sentence := "Mary ate peanuts in 0.43 seconds",
    objectNP := "peanuts",
    objectRef := .cum,
    inXAcceptance := .accept }

/-- The K98 §3.5 eq. 58 witness pattern: CUM object + accepted *in*-X.
    The combination is unusual — typical *in*-X licensing requires QUA
    objects via the K98 §3.3 propagation chain. K98 introduces this
    case to motivate temporal atomicity as an alternative licensing
    pathway. K89 §5 makes the parallel point with *Ann drank wine in
    0.43 sec* (formalized in `Krifka1989.annDrankWineInSeconds`); this
    is K98's same observation reformulated as temporal atomicity. The
    propositional ATM-but-not-QUA witness is deferred (requires
    event-CEM atom infrastructure beyond this file's scope, as
    documented in K89 study §5). -/
theorem k98_eq58_cum_object_accepts_inX :
    maryAtePeanutsIn043Sec.objectRef = Core.Order.MereoTag.cum ∧
    maryAtePeanutsIn043Sec.inXAcceptance = DiagnosticResult.accept := ⟨rfl, rfl⟩

/-! ### K89 ↔ K98 Sister-Paper Bridge -/

/-! K89 (1989) and K98 (1998) are the same author refining the same
    theory at two stages. K89 study now defines
    `K89ThematicClass.toVerbIncClass` in `Studies/Krifka1989.lean`,
    mapping K89's table-14 thematic-relation classes to K98's
    `VerbIncClass`. This section provides the K98-side acknowledgement
    of the bridge: every K89 thematic class corresponds to exactly one
    K98 VerbIncClass, and the refinement is consistent with K89's GRAD
    distinction (gradual classes → sinc/inc, non-gradual → cumOnly).

    The K89 study's `k89Table14_refines_k98_consistently` provides the
    propositional bridge; this section adds K98-side documentation and
    a fragment-verb ↔ K89-class consistency theorem for *eat*. -/

/-- K89's *eat an apple* (gradual-consumed-patient) refines to K98 sinc
    (consumption verb), which matches the *eat* fragment annotation.
    Cross-paper consistency for the eat verb across K89 §4, K98 §3,
    and the fragment. -/
theorem eat_refinement_chain :
    Krifka1989.eatAnApple.thematicClass = .gradualConsumedPatient ∧
    Krifka1989.eatAnApple.thematicClass.toVerbIncClass = .sinc ∧
    eat.toVerb.verbIncClass = some .sinc := ⟨rfl, rfl, rfl⟩

/-- K89's *write a letter* (gradual-effected-patient) refines to K98
    sinc, matching *write*'s fragment annotation. K89's distinction
    between effected (creation) and consumed (consumption) patients
    is finer than K98's binary sinc/non-sinc; both collapse to sinc
    here. -/
theorem write_refinement_chain :
    Krifka1989.writeALetter.thematicClass = .gradualEffectedPatient ∧
    Krifka1989.writeALetter.thematicClass.toVerbIncClass = .sinc ∧
    write.toVerb.verbIncClass = some .sinc := ⟨rfl, rfl, rfl⟩

/-- K89's *read a letter* (gradual-patient, lacks UNI-E) refines to
    K98 inc — matching *read*'s fragment annotation, which K98 §3.6
    eq. 59 motivates by appeal to backups (re-reading). -/
theorem read_refinement_chain :
    Krifka1989.readALetter.thematicClass = .gradualPatient ∧
    Krifka1989.readALetter.thematicClass.toVerbIncClass = .inc ∧
    read.toVerb.verbIncClass = some .inc := ⟨rfl, rfl, rfl⟩

/-! ### Concrete `IsSincVerb` Toy + Applied Propagation -/

/-! §4.5's `eat_apples_cum_propositional` and `eat_two_apples_qua_propositional`
    are parametric over an abstract θ. This section provides a
    constructive `IsSincVerb` instance and *fires* both propagation
    theorems on it, demonstrating that K98 §3.3's typeclass-bundled
    meaning postulates admit real (non-axiomatic) realizations.

    The toy: a 3-apple universe modelled as `Finset (Fin 3)` (powerset
    lattice; ⊔ = ∪, < = ⊊). The eating relation is the identity
    `eatThemeToy a e := a = e` — the eating event is identified with
    the apple set eaten. Each subevent of an eating-of-{0,1}
    corresponds bijectively to a subobject (the apples eaten in that
    subevent), which is exactly the SINC bijection.

    Lexical commitment: this is a TOY model, not a faithful denotation
    of *eat*. A real denotation would (i) use a richer event type with
    manner/agent/time information, (ii) admit non-trivial UO failures
    (two distinct eatings of the same apple), and (iii) interact with
    `Fragments/English/Predicates/Verbal.lean`'s `eat.semantics`. The
    purpose here is to demonstrate that the typeclass admits
    constructive instances — bridging the gap that prior `class
    VerbIncrementality` attempts left open. -/

section ToyEatInstance

/-- Toy 3-apple universe. `Finset (Fin 3)` carries `SemilatticeSup`
    automatically (join is `Finset.union`); `≤`/`<` are `⊆`/`⊊`. -/
abbrev Apple : Type := Finset (Fin 3)

/-- Toy "eating event" — identified with the set of apples eaten.
    Same powerset lattice as `Apple`, yielding the bijection that
    SINC requires. -/
abbrev EatEvent : Type := Finset (Fin 3)

/-- The identity-as-relation theme: `eatThemeToy a e` iff the apple
    set `a` equals the apple set eaten in event `e`. The canonical
    SINC example, exhibiting a 1-1 correspondence between proper
    sub-objects (subsets of `a`) and proper sub-events. -/
def eatThemeToy (a : Apple) (e : EatEvent) : Prop := a = e

/-- The SINC structure for `eatThemeToy`. All five component conditions
    (MSO / UO / MSE / UE / extended) follow from the identity nature
    of the relation. The non-degeneracy condition `extended` is
    witnessed by `{0, 1}` (whole) and `{0}` (proper part). -/
private def eatThemeToy_sinc : SINC eatThemeToy where
  mso := by
    intro x e e' hθ hlt
    refine ⟨e', ?_, rfl⟩
    rw [hθ]; exact hlt
  uo := by
    intro x e e' hθ hle
    refine ⟨e', ?_, rfl, ?_⟩
    · rw [hθ]; exact hle
    · intro z _ hz; exact hz
  mse := by
    intro x e y hθ hlt
    refine ⟨y, ?_, rfl⟩
    rw [← hθ]; exact hlt
  ue := by
    intro x e y hθ hle
    refine ⟨y, ?_, rfl, ?_⟩
    · rw [← hθ]; exact hle
    · intro e'' _ he''; exact he''.symm
  extended := by
    refine ⟨{0, 1}, {0}, {0, 1}, {0}, ?_, ?_, rfl, rfl⟩
    · refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨1, ?_, ?_⟩
      · intro a ha; simp at ha; subst ha; simp
      · simp
      · simp
    · refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨1, ?_, ?_⟩
      · intro a ha; simp at ha; subst ha; simp
      · simp
      · simp

/-- UP for `eatThemeToy`: identity-as-relation gives x = y trivially. -/
private theorem eatThemeToy_up : UP eatThemeToy := by
  intro x y e hx hy
  show x = y
  rw [hx, hy]

/-- CumTheta for `eatThemeToy`: identity-as-relation preserves sums. -/
private theorem eatThemeToy_cumTheta : CumTheta eatThemeToy := by
  intro x y e e' hx hy
  show x ⊔ y = e ⊔ e'
  rw [hx, hy]

/-- `eatThemeToy` is a strictly incremental verb-theme relation.
    Constructed via the `IsSincVerb.mk'` smart constructor, which
    derives the inherited `inc : INC eatThemeToy` field automatically
    via `inc_of_sinc`. -/
instance : IsSincVerb eatThemeToy :=
  IsSincVerb.mk' eatThemeToy_sinc eatThemeToy_up eatThemeToy_cumTheta

/-- Synthesis test: `[IsIncVerb eatThemeToy]` is auto-synthesised from
    the `IsSincVerb` instance via the `extends` chain (K98 §3.6:
    "every SINC verb is also INC"). Fires without explicit derivation. -/
example : IsIncVerb eatThemeToy := inferInstance

/-- Synthesis test: `[IsCumThetaVerb eatThemeToy]` is auto-synthesised
    from the `IsSincVerb` instance via the `extends` chain transitively. -/
example : IsCumThetaVerb eatThemeToy := inferInstance

/-! #### Concrete OBJ predicates -/

/-- "two specific apples" — the singleton predicate `λ a, a = {0, 1}`.
    QUA: no proper subset of `{0, 1}` is also `{0, 1}`. -/
def twoApples : Apple → Prop := fun a => a = ({0, 1} : Finset (Fin 3))

/-- "(some) apples" — non-emptiness in the powerset lattice. CUM:
    nonempty ∪ nonempty is nonempty. The natural bare-plural
    interpretation in this toy. -/
def someApples : Apple → Prop := fun a => a.Nonempty

/-- `twoApples` is QUA: a proper part of `{0, 1}` cannot also equal
    `{0, 1}`. This is the standard "exact-cardinality NPs are
    quantized" property at the K89/K98 level. -/
theorem twoApples_qua : QUA twoApples := by
  intro x y hx hlt hy
  -- hx : x = {0,1}, hy : y = {0,1}, hlt : y < x. Substitute to get y < y.
  rw [hx, hy] at hlt; exact hlt.ne rfl

/-- `someApples` is CUM: nonempty ⊔ nonempty = nonempty. Bare plurals
    propagate cumulativity (K89 §3 / K98 §3.3). -/
theorem someApples_cum : CUM someApples := by
  intro x y hx _hy
  -- hx : x.Nonempty ⇒ x ⊔ y = x ∪ y is nonempty
  exact hx.mono (by intro a ha; exact Finset.mem_union.mpr (Or.inl ha))

/-! #### K98 §3.3 propagation theorems fire on the toy -/

/-- *eat two apples* on the toy: SINC + UP verb + QUA object → QUA VP.
    Direct invocation of substrate's typeclass-canonical
    `qua_propagation`; `[IsSincVerb eatThemeToy]` synthesises
    automatically from the instance above. -/
theorem eat_two_apples_toy_qua : QUA (VP eatThemeToy twoApples) :=
  qua_propagation twoApples_qua

/-- *eat (some) apples* on the toy: CumTheta verb + CUM object → CUM VP.
    Direct invocation of substrate's `cum_propagation`;
    `[IsCumThetaVerb eatThemeToy]` synthesises from `[IsSincVerb …]`
    via `instIsCumThetaVerbOfIsSincVerb`. -/
theorem eat_some_apples_toy_cum : CUM (VP eatThemeToy someApples) :=
  cum_propagation someApples_cum

end ToyEatInstance

/-! ## Part II — K98 §4: Telicity by Precedence and Adjacency -/

/-! ### Per-verb path specification (K98 §4.5 eq. 73) -/

/-- "arrive" is inherently directed motion (K98 §4.7 eq. 78). -/
theorem arrive_levinClass :
    arrive.toVerb.levinClass = some .inherentlyDirectedMotion := rfl

/-- Inherently directed motion → bounded path (K98 §4.5 GOAL specified). -/
theorem arrive_pathSpec :
    LevinClass.inherentlyDirectedMotion.pathSpec = some .bounded := rfl

/-- "leave" is a leave verb (K98 §4.5 SOURCE-only). -/
theorem leave_levinClass :
    leave.toVerb.levinClass = some .leave := rfl

/-- Leave verbs → source path. -/
theorem leave_pathSpec :
    LevinClass.leave.pathSpec = some .source := rfl

/-- "run" is manner-of-motion (K98 §4.5 path-neutral; PP supplies path). -/
theorem run_levinClass :
    run.toVerb.levinClass = some .mannerOfMotion := rfl

/-- Manner-of-motion verbs are path-neutral (path comes from PP). -/
theorem run_pathSpec :
    LevinClass.mannerOfMotion.pathSpec = none := rfl

-- Fragment-grounding drift sentries: changing a fragment annotation in
-- `Fragments/English/Predicates/Verbal.lean` breaks exactly one theorem.

/-- *arrive* is annotated as an achievement Vendler class. -/
theorem arrive_vendlerClass_achievement :
    arrive.toVerb.vendlerClass = some .achievement := rfl

/-- *sleep* is annotated as a state Vendler class. -/
theorem sleep_vendlerClass_state :
    sleep.toVerb.vendlerClass = some .state := rfl

/-! ### PathShape → Telicity → Licensing (K98 §4 MR eq. 71) -/

/-- Bounded path → telic → licensed. K98 §4 eq. 74 *walked from X to Y*. -/
theorem bounded_pipeline :
    pathShapeToTelicity .bounded = .telic ∧
    LicensingPipeline.IsLicensed PathShape.bounded := ⟨rfl, trivial⟩

/-- Source path → telic → licensed. K98 §4 eq. 73 *Mary left the house*. -/
theorem source_pipeline :
    pathShapeToTelicity .source = .telic ∧
    LicensingPipeline.IsLicensed PathShape.source := ⟨rfl, trivial⟩

/-- Unbounded path → atelic → blocked. K98 §4 eq. 75 *walked towards X*. -/
theorem unbounded_pipeline :
    pathShapeToTelicity .unbounded = .atelic ∧
    ¬ LicensingPipeline.IsLicensed PathShape.unbounded := ⟨rfl, id⟩

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
    arrive.toVerb.vendlerClass = some .achievement ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl⟩

/-- "leave" (achievement, source path) licenses "in X". -/
theorem leave_inX :
    leave.toVerb.vendlerClass = some .achievement ∧
    inXPrediction .achievement = .accept := ⟨rfl, rfl⟩

/-- "run" (activity, path-neutral) licenses "for X". -/
theorem run_forX :
    run.toVerb.vendlerClass = some .activity ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl⟩

/-- Motion verb VendlerClass × LevinClass coherence: bounded-path motion
    verbs are achievements, path-neutral ones are activities. -/
theorem motion_vendler_path_coherence :
    (arrive.toVerb.vendlerClass = some .achievement ∧
      LevinClass.inherentlyDirectedMotion.pathSpec = some .bounded) ∧
    (leave.toVerb.vendlerClass = some .achievement ∧
      LevinClass.leave.pathSpec = some .source) ∧
    (run.toVerb.vendlerClass = some .activity ∧
      LevinClass.mannerOfMotion.pathSpec = none) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ### K98 §4 propositional substrate -/

section K98PropositionalSubstrate

open Semantics.ArgumentStructure (MO)

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
    `Semantics.Aspect.PrecedenceClosure` with `cond := precedes`. -/
abbrev MovementClosure {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (precedes : β → β → Prop) (θ' : α → β → Prop) : α → β → Prop :=
  Semantics.Aspect.PrecedenceClosure precedes θ'

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
  ⟨θ, h, fun x e => ⟨Semantics.Aspect.PrecedenceClosure.base,
    fun hcl => Semantics.Aspect.PrecedenceClosure.closure_subset
      (fun _ _ h => h) hClosed hcl⟩⟩

end K98PropositionalSubstrate

/-! ### σ-pullback invocations (bounded/unbounded path → telic/atelic VP) -/

section SpatialTracePullback

open Semantics.Events.CEM
open Semantics.Spatial.Path

variable {Loc Time : Type*} [LinearOrder Time]
variable [cem : EventCEM Time] [SemilatticeSup (Path Loc)]
variable [st : Trace Loc Time]

/-- Bounded path predicate (QUA) ↦ telic VP via the σ-pullback. Backs
    the K98 §4.5 *walked from X to Y* analysis at the Bool-tag level. -/
theorem walked_from_to_telic_propositional
    (hinj : Function.Injective st.σ)
    {P : Path Loc → Prop} (hP : QUA P) :
    @QUA _ cem.evSemilatticeSup.toPartialOrder (P ∘ st.σ) :=
  Trace.bounded_path_telic hinj hP

/-- Unbounded path predicate (CUM) ↦ atelic VP via the σ-pullback. Backs
    the K98 §4.5 *walked towards X* analysis at the Bool-tag level. -/
theorem walked_towards_atelic_propositional
    {P : Path Loc → Prop} (hP : CUM P) :
    @CUM _ cem.evSemilatticeSup (P ∘ st.σ) :=
  Trace.unbounded_path_atelic hP

end SpatialTracePullback

/-! ### EXP / SEINC instances on `Event Time` (K98 §4.1) -/

section Expansiveness

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

end Krifka1998
