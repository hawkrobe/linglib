import Linglib.Theories.Semantics.Events.ThematicRoleProperties
import Linglib.Theories.Semantics.Events.Incrementality
import Linglib.Theories.Semantics.Events.CumulativityPropagation
import Linglib.Theories.Semantics.Events.Mereology
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.TenseAspect.Diagnostics
import Linglib.Phenomena.TenseAspect.Studies.Krifka1989
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic

/-!
# @cite{krifka-1998} *The Origins of Telicity*: §3 Incrementality
@cite{krifka-1998} @cite{krifka-1989} @cite{vendler-1957} @cite{filip-2012}

K98's verb-classification machinery (`VerbIncClass` = sinc/inc/cumOnly)
and §3 telicity propagation theorems, applied to fragment verbs and
diagnostic predictions. The substrate (SUM, UO, UE, MO, MSO, MSE, GUE,
SINC, INC, CumTheta — K98 §3.2 eq. 43-52, eq. 59) lives in
`Theories/Semantics/Events/Krifka1998.lean`; this file exercises it on
the English fragment.

## What this file is

A schema-level study of K98 §3 (incrementality + cumulativity +
quantization propagation):

- **§1-2** Per-verb annotation tripwires (`eat.verbIncClass = some .sinc`
  by `rfl`, etc.) — break exactly one theorem when a fragment annotation
  changes; documentation as much as theorem.
- **§3** VendlerClass → MereoTag bridge via `Telicity.toMereoTag`.
  Caveat: K98 §2.5 (eq. 37) defines TEL strictly weaker than QUA; the
  `Telicity.toMereoTag .telic = .qua` collapse is an approximation
  given that linglib has no propositional `def TEL` substrate yet (a
  faithful TEL would need INI/FIN initial/final-part predicates over
  events, which K98 theory doesn't house). See K98 §2.5 page 9: "every
  quantized predicate is telic ... but not every telic predicate is
  quantized".
- **§4** Compositional telicity. Round-1 audit added: propositional
  invocations of K98 theory's `cum_propagation` and `qua_propagation`
  on abstract θ instances (parallel to K89 study §3's actual calls of
  `qmod_of_cum_is_qua`), instead of stipulated `⟨rfl, rfl⟩` over Bool
  tags.
- **§5** Diagnostic bridge to `Diagnostics.lean`'s for/in predictions.
  General theorems `telic_licenses_inX` and `durative_atelic_licenses_forX`
  carry the work; the round-1 audit deleted 6 per-verb
  `inXPrediction .accomplishment = .accept := rfl`-style theorems that
  were tautological restatements (since `eat_two_apples_licenses_inX`
  and `build_a_house_licenses_inX` had identical statements — both
  passing `.accomplishment` to `inXPrediction`).
- **§6** Cross-verification: VendlerClass × VerbIncClass coherence.
- **Part II** GRAD predictions, with `GRADDatum` now using a `GRADVerb`
  enum instead of a free `String` field (round-1 audit fixed the
  String anti-pattern that round-2 had recreated from the K89 study
  round-2 fix).
- **§7** Eq. 58 *Mary ate peanuts in 0.43 seconds* — K98's own version
  of K89's *Ann drank wine in 0.43 sec* showing that **temporal
  atomicity** (not quantization) is what licenses *in*-X. The K89 study
  has an analogous section anchored on K89 §5 / T4; this file mirrors
  it for K98 §3.5 page 18.
- **§8** K89 ↔ K98 sister-paper bridge. K89 study now defines
  `K89ThematicClass.toVerbIncClass` mapping K89's table-14 thematic
  classes into K98's `VerbIncClass`; this file confirms the refinement
  is well-typed via a back-reference theorem.
- **§9** Concrete `IsSincVerb` toy + applied propagation. A 3-apple
  powerset lattice with identity-as-relation `eatThemeToy` provides a
  fully proven `IsSincVerb` instance — the constructive witness that
  K98 §3.3's typeclass-bundled meaning postulates admit non-axiomatic
  realizations. Two applied theorems then *fire* §4.5's parametric
  `eat_two_apples_qua_propositional` and `eat_apples_cum_propositional`
  on this concrete verb, demonstrating the K98 propagation chain on a
  real (kernel-checkable) relation rather than only on abstract θ.

## Caveat: `cumOnly` is the formaliser's term, not K98's

K98 nowhere uses the literal label "cumOnly". The paper distinguishes
verbs that are merely cumulative (CUM, eq. 44) without strict
incrementality (¬SINC, ¬MSE) from incremental ones. *push*, *pull*,
*carry* are CUM-but-not-incremental in K98's vocabulary. The
`VerbIncClass.cumOnly` constructor name is shorthand for "cumulative
without incrementality" — convenient but anachronistic with respect to
K98's own writing.

## What this file is NOT

- Not a §4 paper-replication — that's `Studies/Krifka1998Movement.lean`
  (paths/movement/quality-changes via the σ-trace substrate). K98 §4
  (Telicity by Precedence and Adjacency) is K98's distinctive
  contribution beyond K89. Together this file (§3) and Krifka1998Movement
  (§4) cover the paper.
- Not a critique of K98's classification — that's `Studies/Filip2012.lean`,
  which proves Filip's three-way (CUM, QUA, ¬CUM ∧ ¬QUA) classification
  via K98 theory §10's propagation gap.
- Not a fragment-only verb-annotation file — the fragment annotations
  in `Fragments/English/Predicates/Verbal.lean` are tested per-verb
  here as a tripwire layer.

-/

namespace Krifka1998

open Fragments.English.Predicates.Verbal
open Core.Verbs
open Semantics.Events.ThematicRoleProperties (UP CumTheta IsCumThetaVerb)
open Semantics.Events.Incrementality (SINC VerbIncClass IsSincVerb IsIncVerb)
open Semantics.Events.CumulativityPropagation (VP cum_propagation qua_propagation)
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction DiagnosticResult)

-- ════════════════════════════════════════════════════
-- § 1. Per-Verb Incrementality Verification
-- ════════════════════════════════════════════════════

/-! Each verb's `verbIncClass` annotation is verified by `rfl`. Changing
    any annotation breaks exactly one theorem here. These earn their
    place as fragment-annotation tripwires; mathlib would call them
    `example`s, but as `theorem`s they're discoverable via `#check`. -/

/-- "eat" is strictly incremental (consumption: bijective theme-event map). -/
theorem eat_sinc : eat.toVerbCore.verbIncClass = some .sinc := rfl

/-- "devour" is strictly incremental (consumption variant of eat). -/
theorem devour_sinc : devour.toVerbCore.verbIncClass = some .sinc := rfl

/-- "build" is strictly incremental (creation: bijective theme-event map). -/
theorem build_sinc : build.toVerbCore.verbIncClass = some .sinc := rfl

/-- "write" is strictly incremental (creation verb). -/
theorem write_sinc : write.toVerbCore.verbIncClass = some .sinc := rfl

/-- "read" is incremental but not strictly so (allows re-reading per K98 §3.6). -/
theorem read_inc : read.toVerbCore.verbIncClass = some .inc := rfl

/-- "push" is cumulative only (no incremental theme — the formaliser's
    "cumOnly" is shorthand; K98 calls it CUM-without-MSE/MSO). -/
theorem push_cumOnly : push.toVerbCore.verbIncClass = some .cumOnly := rfl

/-- "pull" is cumulative only. -/
theorem pull_cumOnly : pull.toVerbCore.verbIncClass = some .cumOnly := rfl

/-- "carry" is cumulative only. -/
theorem carry_cumOnly : carry.toVerbCore.verbIncClass = some .cumOnly := rfl

/-- "drag" is cumulative only. -/
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

-- ════════════════════════════════════════════════════
-- § 4. Compositional Telicity (VP = verb + NP)
-- ════════════════════════════════════════════════════

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
    eat.toVerbCore.verbIncClass = some .sinc ∧
    VendlerClass.activity.telicity.toMereoTag = .cum := ⟨rfl, rfl⟩

/-- "eat two apples": sinc verb + QUA NP → QUA VP (telic).
    K98 §3.3: SINC(θ) ∧ QUA(OBJ) → QUA(VP θ OBJ).
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
    when the object is quantized, K98 §3.6). -/
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

/-! ### §4.5 Propositional propagation invocations (typeclass form)

    The Bool-tag conjunctions above check fragment annotations and tag
    composition; the theorems below actually invoke K98 theory's
    `cum_propagation` and `qua_propagation` (typeclass-canonical
    forms) on abstract θ + OBJ instances. This is the same shape as
    K89 study §3's calls of `qmod_of_cum_is_qua` — making the
    substrate-bridge promise concrete rather than rhetorical. -/

section PropositionalPropagation

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
open Mereology

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

-- ════════════════════════════════════════════════════
-- § 5. Diagnostic Bridge
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- Part II: Gradual Change (GRAD) Predictions
-- ════════════════════════════════════════════════════

/-! Connects GRAD/GRADSquare theory from `Events/Krifka1998.lean` and
    `Events/Krifka1989.lean` to concrete verb entries.

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
    GRADVerb.eat.expectedIncClass = eat.toVerbCore.verbIncClass ∧
    GRADVerb.build.expectedIncClass = build.toVerbCore.verbIncClass ∧
    GRADVerb.read.expectedIncClass = read.toVerbCore.verbIncClass ∧
    GRADVerb.push.expectedIncClass = push.toVerbCore.verbIncClass ∧
    GRADVerb.kick.expectedIncClass = kick.toVerbCore.verbIncClass :=
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
    predicate (`Theories/Semantics/Events/Krifka1998.lean:256`); the
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
    predictsGRAD eat.toVerbCore.verbIncClass = true := rfl
theorem build_predicts_grad :
    predictsGRAD build.toVerbCore.verbIncClass = true := rfl
theorem read_predicts_grad :
    predictsGRAD read.toVerbCore.verbIncClass = true := rfl
theorem push_no_grad :
    predictsGRAD push.toVerbCore.verbIncClass = false := rfl
theorem kick_no_grad :
    predictsGRAD kick.toVerbCore.verbIncClass = false := rfl

/-- All GRAD data matches the K98-expected verb classification. The
    `decide` closure works because `verb.expectedIncClass` is
    structurally reducible (literal-tag enum), unlike a fragment-
    projection that goes through `Verbal.lean`'s `VerbEntry`. The
    fragment-annotation tripwire is `gradVerb_matches_fragment`. -/
theorem all_grad_data_matches :
    gradData.all (fun d => predictsGRAD d.verb.expectedIncClass == d.expectsGRAD) = true := by
  decide

-- ════════════════════════════════════════════════════
-- § 7. K98 §3.5 Eq. 58: Mary ate peanuts in 0.43 seconds
-- ════════════════════════════════════════════════════

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
  objectRef : Core.Scale.MereoTag
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
    maryAtePeanutsIn043Sec.objectRef = Core.Scale.MereoTag.cum ∧
    maryAtePeanutsIn043Sec.inXAcceptance = DiagnosticResult.accept := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 8. K89 ↔ K98 Sister-Paper Bridge
-- ════════════════════════════════════════════════════

/-! K89 (1989) and K98 (1998) are the same author refining the same
    theory at two stages. K89 study now defines
    `K89ThematicClass.toVerbIncClass` (`Studies/Krifka1989.lean:457`)
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
    eat.toVerbCore.verbIncClass = some .sinc := ⟨rfl, rfl, rfl⟩

/-- K89's *write a letter* (gradual-effected-patient) refines to K98
    sinc, matching *write*'s fragment annotation. K89's distinction
    between effected (creation) and consumed (consumption) patients
    is finer than K98's binary sinc/non-sinc; both collapse to sinc
    here. -/
theorem write_refinement_chain :
    Krifka1989.writeALetter.thematicClass = .gradualEffectedPatient ∧
    Krifka1989.writeALetter.thematicClass.toVerbIncClass = .sinc ∧
    write.toVerbCore.verbIncClass = some .sinc := ⟨rfl, rfl, rfl⟩

/-- K89's *read a letter* (gradual-patient, lacks UNI-E) refines to
    K98 inc — matching *read*'s fragment annotation, which K98 §3.6
    eq. 59 motivates by appeal to backups (re-reading). -/
theorem read_refinement_chain :
    Krifka1989.readALetter.thematicClass = .gradualPatient ∧
    Krifka1989.readALetter.thematicClass.toVerbIncClass = .inc ∧
    read.toVerbCore.verbIncClass = some .inc := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 9. Concrete `IsSincVerb` Toy + Applied Propagation
-- ════════════════════════════════════════════════════

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

open Mereology (CUM QUA)

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

-- ────────────────────────────────────────────────────
-- §9.1 Concrete OBJ predicates
-- ────────────────────────────────────────────────────

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

-- ────────────────────────────────────────────────────
-- §9.2 K98 §3.3 propagation theorems fire on the toy
-- ────────────────────────────────────────────────────

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

end Krifka1998
