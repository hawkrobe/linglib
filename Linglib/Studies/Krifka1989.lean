import Linglib.Semantics.Mereology
import Linglib.Semantics.Events.Basic
import Linglib.Semantics.Plurality.Algebra
import Linglib.Semantics.ArgumentStructure.Properties
import Linglib.Semantics.Aspect.Incremental
import Linglib.Semantics.Aspect.Cumulativity
import Linglib.Core.Order.Boundedness
import Linglib.Features.Aktionsart

/-!
# [krifka-1989] "Nominal Reference, Temporal Constitution and Quantification"

K89's algebraic semantics tying nominal-reference properties (CUM/QUA
via §3 mass/count/bare-plural) to verbal aspect (CUM/QUA on VPs via §4
thematic-relation properties + §5 temporal-trace homomorphisms). A
schema-level study: each section either records data (NP/verb/reading
items with enumerated source kinds) or calls a propositional theorem
on abstract domains.

## Main definitions

* `NPDatum` + `k89NPData` — 15 NPs from K89 §3 (mass/count/measure/definite)
* `qmod_qua` / `qmod_of_cum_is_qua` / `measure_phrase_makes_qua` — K89 §2-§3
  measure-phrase substrate (T6 + D28; inlined from former
  `Events/MeasurePhrases.lean`)
* `K89ThematicClass` + `K89ThematicDatum` + `k89Table14` — K89 §4 eq. 14 verbs
  (write/eat/read/touch/see) with feature profiles {SUM, GRAD, UNI-E}
* `ATM` + `qua_implies_atm` — K89 D17/D18/T4 atomicity (§5 *in*-X licensing)
* `K89ThematicClass.toVerbIncClass` — K89 → K98 refinement bridge
* `K89QuantDatum` + `k89Section7Data` — K89 §7 quantification data items

## TODO

* **K89 GRAD propositional chain**: `SINC + ExtMeasure + MeasureProportional →
  GRAD` was deleted in 0.231.55 (formerly in `Events/GradualChange.lean`,
  zero-consumer); the Bool-tag proxy in `Studies/Krifka1998.lean` is also gone.
  A future K89 §4 propositional-faithfulness pass needs to rebuild it.
* **K89↔Champollion `forAdverbial_subsumes_qmod` bridge**: also dropped in
  0.231.55 as dead. ~5 LOC over `forAdverbialMeaning` + `QMOD` to
  re-derive when a Champollion replication wants the cross-framework bridge.
* **K89 §7 quantification** (max/MXE/MXT/cumulative-distributive
  derivations): registered as data here; full formalization left to a
  successor file naturally clustering with Plurals/Quantification.
* **GRAD collapse caveat (§ 4)**: `ThematicProfile` collapses K89's
  5-tuple {SUM, UNI-O, UNI-E, MAP-O, MAP-E} to 3-tuple {SUM, GRAD,
  UNI-E}. K89 D35 has GRAD ↔ UNI-O ∧ MAP-O ∧ MAP-E. K89 T11/T12 use
  UNI-O and MAP-O *individually*; the unbundled form is needed there.
* **Atomicity-without-quantization witness**: § 5 explains that *Ann drank
  wine in 0.43 seconds* is ATM-but-not-QUA, but the substrate witness
  requires event-CEM atom infrastructure beyond this file's scope.

## What this file is NOT

* Not a verb-classification study (that's `Studies/Krifka1998.lean`'s
  `VerbIncClass`; the K89 → K98 refinement bridge in § 4 makes the
  connection explicit).
* Not a *for*-X / *in*-X diagnostic study (that's
  `Features/Aktionsart.lean`).
* Not a critique of K89's binary CUM/QUA (that's `Studies/Filip2012.lean`,
  which proves the three-way classification's middle ground stable).

## References

* [krifka-1989] (primary, anchor for this file)
* Sister: `Studies/Krifka1998.lean` (K98, same-author 9-years-later
  refinement; covers both §3 incrementality and §4 motion);
  `Studies/Filip2012.lean` (three-way classification critique).
-/

namespace Krifka1989

open _root_.Mereology
open Semantics.Plurality.Algebra (Materialization)
open Semantics.ArgumentStructure (UP)
open Semantics.Aspect.Incremental (SINC VerbIncClass IsSincVerb)
open Semantics.Aspect.Cumulativity (VP qua_propagation)
open Core.Order (MereoTag)
open Features
  (forXPrediction inXPrediction DiagnosticResult)

/-! ### K89 measure-phrase substrate (inlined from Events/MeasurePhrases.lean in 0.231.55) -/

/-- QMOD produces QUA predicates when μ is extensive and n > 0.
    [krifka-1989] §2: "three kilos of rice" is QUA because no
    proper part of a 3kg entity also weighs 3kg (extensivity of
    weight). -/
theorem qmod_qua {α : Type*} [SemilatticeSup α]
    {R : α → Prop} {μ : α → ℚ} [hμ : ExtMeasure α μ]
    {n : ℚ} (_hn : 0 < n) :
    QUA (QMOD R μ n) :=
  Mereology.qmod_qua R n

/-- A CUM mass noun combined with QMOD (via an extensive measure)
    yields a QUA measure phrase. [krifka-1989] §3 D28. -/
theorem qmod_of_cum_is_qua {α : Type*} [SemilatticeSup α]
    {R : α → Prop} (_hCum : CUM R)
    {μ : α → ℚ} [ExtMeasure α μ]
    {n : ℚ} (hn : 0 < n) :
    QUA (QMOD R μ n) :=
  qmod_qua hn

/-- **K89 measure-phrase chain**: QMOD(mass_noun, extensive_μ, n) +
    `[IsSincVerb θ]` → QUA VP (telic). Central K89 result: measure
    phrases turn mass nouns into quantized predicates, and quantization
    propagates through strictly incremental verbs to yield telic VPs. -/
theorem measure_phrase_makes_qua {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {R : α → Prop} (hCum : CUM R)
    {μ : α → ℚ} [ExtMeasure α μ]
    {n : ℚ} (hn : 0 < n)
    {θ : α → β → Prop} [IsSincVerb θ] :
    QUA (VP θ (QMOD R μ n)) :=
  qua_propagation (qmod_of_cum_is_qua hCum hn)

/-! ### Nominal Reference Classification (K89 §3) -/

/-- Why an NP has the reference type it does, per [krifka-1989] §3.
    Each constructor names the structural source of CUM or QUA reference.
    Replaces a free-form `String` justification field with an enumerated
    typology so per-source consistency can be checked.

    Note: §7 proportional quantifiers (*most girls*, *less than three
    girls*) are intentionally NOT a constructor here. K89 §7 gives them
    maximal-event semantics (D44 MXT, D45 MXE, D46 max), not §3 CUM/QUA
    classification. They live in `K89QuantDatum` (§6) as sentence-level
    data without a §3 reference type. -/
inductive NPRefSource where
  | massNoun        -- CUM via mass-noun semantics
  | barePlural      -- CUM via algebraic closure (*P)
  | countNumeral    -- QUA via count noun + numeral
  | measurePhrase   -- QUA via QMOD on extensive measure (D28)
  | definite        -- QUA via singular maximal individual (§7)
  | singularCount   -- QUA via singular count noun
  deriving DecidableEq, Repr

/-- The structural source uniquely determines CUM vs QUA per K89 §3.
    Mass nouns and bare plurals are CUM; count, measured, definite
    NPs are QUA. -/
def NPRefSource.expectedRef : NPRefSource → MereoTag
  | .massNoun       => .cum
  | .barePlural     => .cum
  | .countNumeral   => .qua
  | .measurePhrase  => .qua
  | .definite       => .qua
  | .singularCount  => .qua

/-- An NP datum: English form, mereological reference tag, structural
    source. The `source` field justifies the `refType` per K89 §3, and
    `all_nps_consistent_with_source` verifies they agree. -/
structure NPDatum where
  np : String
  refType : MereoTag
  source : NPRefSource
  deriving Repr, BEq

/-- "apples" — bare plural, CUM via algebraic closure. -/
def applesNP : NPDatum := { np := "apples", refType := .cum, source := .barePlural }

/-- "two apples" — count noun + numeral, QUA. -/
def twoApplesNP : NPDatum := { np := "two apples", refType := .qua, source := .countNumeral }

/-- "water" — mass noun, CUM. -/
def waterNP : NPDatum := { np := "water", refType := .cum, source := .massNoun }

/-- "three kilos of water" — QMOD on extensive measure, QUA. K89 §3 D28. -/
def threeKilosWaterNP : NPDatum := { np := "three kilos of water", refType := .qua, source := .measurePhrase }

/-- "a house" — singular count noun, QUA. -/
def aHouseNP : NPDatum := { np := "a house", refType := .qua, source := .singularCount }

/-- "houses" — bare plural, CUM. -/
def housesNP : NPDatum := { np := "houses", refType := .cum, source := .barePlural }

/-- "rice" — mass noun, CUM. K89 §3 paradigm example. -/
def riceNP : NPDatum := { np := "rice", refType := .cum, source := .massNoun }

/-- "the cart" — singular count noun + definite, QUA via singular reference. -/
def theCartNP : NPDatum := { np := "the cart", refType := .qua, source := .singularCount }

/-! K89 §4 table 14 NP exemplars (eq. 14, p. 96): NPs that pair with
    the five thematic-class verbs. -/

/-- "a letter" — singular count, QUA. K89 (12-13), §4 table example. -/
def aLetterNP : NPDatum := { np := "a letter", refType := .qua, source := .singularCount }

/-- "an apple" — singular count, QUA. K89 (14), gradual-consumed-patient row
    (*eat an apple*). -/
def anAppleNP : NPDatum := { np := "an apple", refType := .qua, source := .singularCount }

/-- "a cat" — singular count, QUA. K89 (14), affected-patient row
    (*touch a cat*). -/
def aCatNP : NPDatum := { np := "a cat", refType := .qua, source := .singularCount }

/-- "a horse" — singular count, QUA. K89 (14), stimulus row (*see a horse*). -/
def aHorseNP : NPDatum := { np := "a horse", refType := .qua, source := .singularCount }

/-! K89 §5 NP exemplars (eq. 19, p. 99): the wine pair used to argue
    atomicity ≠ quantization. -/

/-- "wine" — mass noun, CUM. K89 §5 (*drink wine*). The §5 punchline
    *Ann drank wine in 0.43 seconds* shows that the *in*-X licensing
    condition is ATM (atomicity), not QUA — see §5 below. -/
def wineNP : NPDatum := { np := "wine", refType := .cum, source := .massNoun }

/-- "a glass of wine" — measure construction, QUA. K89 §5 contrast
    partner to *wine*. -/
def aGlassOfWineNP : NPDatum := { np := "a glass of wine", refType := .qua, source := .measurePhrase }

/-- "seven apples" — count + numeral, QUA. K89 §7 cumulative-reading
    object NP (*two girls ate seven apples*, eq. 37). -/
def sevenApplesNP : NPDatum := { np := "seven apples", refType := .qua, source := .countNumeral }

/-- All NP data items registered by §3 classification. Excludes K89 §7
    proportional quantifiers (those live in §6 `K89QuantDatum` data). -/
def k89NPData : List NPDatum :=
  [applesNP, twoApplesNP, waterNP, threeKilosWaterNP,
   aHouseNP, housesNP, riceNP, theCartNP,
   aLetterNP, anAppleNP, aCatNP, aHorseNP,
   wineNP, aGlassOfWineNP, sevenApplesNP]

/-- Each NP's `refType` matches its structural source per K89 §3.
    Catches typos and mis-classifications when the data list grows. -/
theorem all_nps_consistent_with_source :
    k89NPData.all (fun d => d.source.expectedRef == d.refType) = true := by
  decide

/-! ### Grounding in K89 Theory's propositional predicates -/

/-! These theorems exercise the K89 theory file's propositional
    predicates on abstract domains, bridging the file-level Bool-tag
    classification (`MereoTag.cum`/`.qua`) to K89's algebraic content
    (`CUM`/`QUA` on `α → Prop`). The `applesNP.refType = .cum` Bool tag
    corresponds to the propositional claim `CUM (AlgClosure P)` for any
    apples-like `P`, which follows from `Mereology.algClosure_cum`. -/

section Grounding

variable {α : Type*}

/-- Bare-plural NPs are cumulative: K89 §3 derives this from algebraic
    closure (*P closed under sum), `Mereology.algClosure_cum`. -/
theorem barePlural_grounded [SemilatticeSup α] {P : α → Prop} :
    CUM (AlgClosure P) :=
  algClosure_cum

end Grounding

/-! ### Measure phrases — exercise qmod / measure_phrase_makes_qua -/

/-! K89 §3 derives that measure phrases like *three kilos of rice* are
    quantized via D28 (QMOD, §3 p. 82) and the upstream T6 (extensive
    measure → quantized, §2 p. 80). These theorems CALL the K89 theory
    file's `qmod_of_cum_is_qua` and `measure_phrase_makes_qua` on an
    abstract `[ExtMeasure α μ]` instance — the docstring promise the
    previous file's `measure_phrase_qua` (which was just `⟨rfl, rfl⟩`
    on stipulated fields) failed to honor. -/

section MeasurePhrases

variable {α β : Type*} [SemilatticeSup α]

/-- *Three kilos of rice* is QUA: a CUM mass noun + an extensive measure
    + a positive value yields a quantized predicate. Direct call to
    `qmod_of_cum_is_qua` (K89 theory §2). -/
theorem threeKilosRice_qua_via_qmod
    {Rice : α → Prop} (hRice : CUM Rice)
    {μ : α → ℚ} [ExtMeasure α μ] :
    QUA (QMOD Rice μ 3) :=
  qmod_of_cum_is_qua hRice (by norm_num)

/-- *Eat three kilos of rice* is QUA: K89's full chain — CUM noun + QMOD
    via extensive measure → QUA NP, then `[IsSincVerb θ]` propagates
    QUA to the VP. Direct call to `measure_phrase_makes_qua` (K89
    theory §4, typeclass-canonical form). -/
theorem eatThreeKilosRice_qua_vp [SemilatticeSup β]
    {Rice : α → Prop} (hRice : CUM Rice)
    {μ : α → ℚ} [ExtMeasure α μ]
    {θ : α → β → Prop} [IsSincVerb θ] :
    QUA (VP θ (QMOD Rice μ 3)) :=
  measure_phrase_makes_qua hRice (by norm_num)

end MeasurePhrases

/-! ### K89 §4 thematic-relation features (eq. 14, p. 96) -/

/-! K89 §4 (eq. 14, p. 96) classifies thematic relations by a feature
    profile {SUM, UNI-O, UNI-E, MAP-O, MAP-E}, with GRAD = UNI-O ∧ MAP-O
    ∧ MAP-E (D35). The five rows of K89's table:

    | example         | SUM | GRAD | UNI-E | label                    |
    |-----------------|-----|------|-------|--------------------------|
    | write a letter  |  X  |  X   |  X    | gradual effected patient |
    | eat an apple    |  X  |  X   |  X    | gradual consumed patient |
    | read a letter   |  X  |  X   |  -    | gradual patient          |
    | touch a cat     |  X  |  -   |  -    | affected patient         |
    | see a horse     |  X  |  -   |  -    | stimulus                 |

    These five labels are K89's thematic-relation classes. The
    propositional predicates (SUM, UP, MO, MSO, MSE, UE, UO, GUE) are
    K89 D29-D35 (§4, pp. 92-96) and live in
    `Studies/Krifka1998.lean` for organizational reasons. Below, each class is captured as a Bool feature profile;
    a successor study could instantiate the propositional predicates
    on concrete θ relations.

    **GRAD collapse caveat.** The `ThematicProfile` collapses K89's
    5-tuple {SUM, UNI-O, UNI-E, MAP-O, MAP-E} to 3-tuple {SUM, GRAD,
    UNI-E}. K89 D35 defines GRAD ↔ UNI-O ∧ MAP-O ∧ MAP-E, and all five
    table-14 verbs happen to align on UNI-O/MAP-O/MAP-E (they co-vary).
    But K89 T11 (p. 95) and T12 use UNI-O and MAP-O *individually* as
    antecedent conditions (not bundled as GRAD). A future formalization
    of T11/T12 will need the unbundled version. -/

inductive K89ThematicClass where
  | gradualEffectedPatient   -- write a letter
  | gradualConsumedPatient   -- eat an apple
  | gradualPatient           -- read a letter
  | affectedPatient          -- touch a cat
  | stimulus                 -- see a horse
  deriving DecidableEq, Repr

/-- Bool-tag profile of K89 §4 features. `hasGRAD` abbreviates
    `hasUNI_O ∧ hasMAP_O ∧ hasMAP_E` (K89 D35), faithful for table 14
    rows where the three components co-vary; see the docstring caveat
    above. -/
structure ThematicProfile where
  hasSUM : Bool
  hasGRAD : Bool
  hasUNI_E : Bool
  deriving Repr, DecidableEq

/-- K89 §4 table-14 feature profiles. -/
def K89ThematicClass.profile : K89ThematicClass → ThematicProfile
  | .gradualEffectedPatient => { hasSUM := true,  hasGRAD := true,  hasUNI_E := true  }
  | .gradualConsumedPatient => { hasSUM := true,  hasGRAD := true,  hasUNI_E := true  }
  | .gradualPatient         => { hasSUM := true,  hasGRAD := true,  hasUNI_E := false }
  | .affectedPatient        => { hasSUM := true,  hasGRAD := false, hasUNI_E := false }
  | .stimulus               => { hasSUM := true,  hasGRAD := false, hasUNI_E := false }

/-- The five K89 (1989) §4 verbs forming K89's table-14 classification.
    Used to derive verb strings in `K89ThematicDatum.vp` instead of
    storing the English form as a free `String`. -/
inductive K89Verb where
  | write  -- gradual effected patient (creation)
  | eat    -- gradual consumed patient
  | read   -- gradual patient (no UE)
  | touch  -- affected patient
  | see    -- stimulus
  deriving DecidableEq, Repr

/-- English lemma for each K89 §4 verb. -/
def K89Verb.lemma : K89Verb → String
  | .write => "write"
  | .eat   => "eat"
  | .read  => "read"
  | .touch => "touch"
  | .see   => "see"

/-- A K89 §4 verb-NP datum: the verb (enumerated), the thematic class
    K89 assigns it, and the NP it pairs with in K89's exemplars. The
    English `vp` string is *derived* from `verb.lemma` and `npDatum.np`
    rather than stored separately — making typos impossible. -/
structure K89ThematicDatum where
  verb : K89Verb
  thematicClass : K89ThematicClass
  npDatum : NPDatum
  deriving Repr

/-- The English VP, derived from the verb lemma and NP. -/
def K89ThematicDatum.vp (d : K89ThematicDatum) : String :=
  d.verb.lemma ++ " " ++ d.npDatum.np

def writeALetter : K89ThematicDatum :=
  { verb := .write, thematicClass := .gradualEffectedPatient, npDatum := aLetterNP }

def eatAnApple : K89ThematicDatum :=
  { verb := .eat, thematicClass := .gradualConsumedPatient, npDatum := anAppleNP }

def readALetter : K89ThematicDatum :=
  { verb := .read, thematicClass := .gradualPatient, npDatum := aLetterNP }

def touchACat : K89ThematicDatum :=
  { verb := .touch, thematicClass := .affectedPatient, npDatum := aCatNP }

def seeAHorse : K89ThematicDatum :=
  { verb := .see, thematicClass := .stimulus, npDatum := aHorseNP }

def k89Table14 : List K89ThematicDatum :=
  [writeALetter, eatAnApple, readALetter, touchACat, seeAHorse]

/-- Derived VPs match the expected English exemplars from K89 (14). -/
theorem k89Table14_vps :
    writeALetter.vp = "write a letter" ∧
    eatAnApple.vp = "eat an apple" ∧
    readALetter.vp = "read a letter" ∧
    touchACat.vp = "touch a cat" ∧
    seeAHorse.vp = "see a horse" := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every K89 thematic class has SUM (cumulativity for thematic relations);
    K89 §4 treats SUM as the foundational property of thematic roles. -/
theorem all_classes_have_sum :
    k89Table14.all (fun d => d.thematicClass.profile.hasSUM) = true := by
  decide

/-- Gradual classes (effected, consumed, plain) all have GRAD; affected
    and stimulus do not. K89 §4 distinction. -/
theorem gradual_classes_have_grad :
    K89ThematicClass.gradualEffectedPatient.profile.hasGRAD = true ∧
    K89ThematicClass.gradualConsumedPatient.profile.hasGRAD = true ∧
    K89ThematicClass.gradualPatient.profile.hasGRAD = true := ⟨rfl, rfl, rfl⟩

theorem nongradual_classes_lack_grad :
    K89ThematicClass.affectedPatient.profile.hasGRAD = false ∧
    K89ThematicClass.stimulus.profile.hasGRAD = false := ⟨rfl, rfl⟩

/-- Effected and consumed patients are distinguished from plain gradual
    patients by UNI-E (uniqueness of events): each subevent of writing
    or eating produces a unique consumed/produced sub-object. *Read a
    letter* allows the same letter-segment to be read multiple times,
    so it lacks UNI-E. -/
theorem uni_e_distinguishes_effected_consumed :
    K89ThematicClass.gradualEffectedPatient.profile.hasUNI_E = true ∧
    K89ThematicClass.gradualConsumedPatient.profile.hasUNI_E = true ∧
    K89ThematicClass.gradualPatient.profile.hasUNI_E = false := ⟨rfl, rfl, rfl⟩

/-! ### K89 → K98 refinement (sister-paper bridge)

    K89 (1989) and K98 (*Origins of Telicity*, 1998) are the same
    author refining the same theory at two stages. K98's `VerbIncClass`
    (`sinc | inc | cumOnly`) is a coarsening of K89's table-14
    five-class scheme. The mapping below makes the refinement explicit:
    *gradual effected/consumed* → SINC (strict bijection between
    object parts and event parts, K98 §3.2 eq. 51), *gradual patient*
    (lacking UNI-E) → INC (general incrementality, K98 §3.6, allows
    re-reading), *affected patient* and *stimulus* (lacking GRAD) →
    cumOnly (no incremental theme, K98 §3.2). -/

/-- Refine K89's 5-class scheme to K98's 3-class enum. K89's 1989 paper
    distinguishes effected from consumed patients (creation vs.
    consumption), but they share the SINC profile in K98's coarser
    classification. -/
def K89ThematicClass.toVerbIncClass : K89ThematicClass → VerbIncClass
  | .gradualEffectedPatient => .sinc
  | .gradualConsumedPatient => .sinc
  | .gradualPatient         => .inc
  | .affectedPatient        => .cumOnly
  | .stimulus               => .cumOnly

/-- The K89 → K98 refinement is consistent with K89's GRAD distinction:
    SINC verbs all have GRAD (consumption/creation gives bijection);
    cumOnly verbs all lack GRAD (no theme-event mapping); INC verbs
    have GRAD without UNI-E (re-reading allowed). -/
theorem toVerbIncClass_respects_grad (cls : K89ThematicClass) :
    (cls.toVerbIncClass = .sinc ∨ cls.toVerbIncClass = .inc) ↔
    cls.profile.hasGRAD = true := by
  cases cls <;> decide

/-- Every K89 verb-NP datum maps to a K98 `VerbIncClass` consistently. -/
theorem k89Table14_refines_k98_consistently :
    k89Table14.all (fun d =>
      (d.thematicClass.toVerbIncClass = .sinc) ||
      (d.thematicClass.toVerbIncClass = .inc) ||
      (d.thematicClass.toVerbIncClass = .cumOnly)) = true := by
  decide

/-! ### Atomicity ≠ Quantization (K89 §5 eq. 19; K89 T4) -/

/-! K89 §5 (around eq. 19, *Ann drank wine in 0.43 seconds*) makes a
    crucial point that a surface QUA → in-X / CUM → for-X classification
    papers over: time-span adverbials require **atomicity** (ATM), not
    quantization (QUA). The QUA → ATM direction is K89 T4 (§2 p. 78,
    listed among "easily checked" theorems); the lifted form for VPs
    via thematic relations is K89 T13 (§4 p. 95). The reverse
    (ATM → QUA) does *not* hold: a predicate can be ATM without being
    QUA.

    Concretely: *Ann drank wine in 0.43 seconds* is acceptable because
    the predicate `λ e. drink-wine(e) ∧ τ(e) ≤ 0.43sec` is atomic — no
    shorter event is also a 0.43-second wine-drinking — even though
    `wine` itself is CUM (mass noun, *not* QUA). The QUA-via-D28 chain
    is one route to ATM, not the only route. -/

section Atomicity

variable {α : Type*} [PartialOrder α]

/-- K89 D17: y is a P-atom — `Mereology.atomize P` (the P-relative `Minimal`):
    y satisfies P and has no proper part also satisfying P. Distinct from
    `Mereology.Atom` (the *absolute* no-proper-part predicate, ignoring P). -/
abbrev AtomicForP (P : α → Prop) (y : α) : Prop := Mereology.atomize P y

/-- K89 D18: ATM(P) — P has atomic reference: every P-instance has a
    P-atomic part. The licensing condition for time-span (*in*-X)
    adverbials per K89 §5. -/
def ATM (P : α → Prop) : Prop :=
  ∀ x, P x → ∃ y, y ≤ x ∧ AtomicForP P y

/-- K89 T4 (§2 p. 78, "easily checked"): every quantized predicate is
    atomic. Witness: any QUA-instance is itself a P-atom (QUA forbids
    proper P-parts), so it is its own atomic-part witness. -/
theorem qua_implies_atm {P : α → Prop} (hQua : QUA P) : ATM P := by
  intro x hPx
  refine ⟨x, le_refl x, hPx, ?_⟩
  intro z hPz hzx
  rcases eq_or_lt_of_le hzx with rfl | hlt
  · exact le_refl _
  · exact (hQua hPz hPx hlt.ne hlt.le).elim

/-! The ATM-but-not-QUA case is genuinely possible — that's this
    section's point. K89's *Ann drank wine in 0.43 seconds* shows that
    a bounded-duration predicate can be ATM (no shorter sub-event is
    also a 0.43-second wine-drinking) without being QUA on the
    underlying object NP (wine is CUM). The substrate-witness theorem
    requires event-CEM atom infrastructure beyond this file's scope;
    the *Ann drank wine* exemplar below stands as the linguistic
    motivation. -/

end Atomicity

/-! ### K89 §3/§5 Materialization Homomorphisms

K89 page 87 introduces a function `h : I → Q` mapping individuals to
their constitutive matter, with `Q(x) → h(x) = x` (identity on
Q-elements) and `h(x ∪ y) = h(x) ∪_Q h(y)` (join preservation). K89
§5 D40 (page 96) introduces the temporal trace `τ : E → T` with the
same shape: `τ(e ∪ e') = τ(e) ∪_T τ(e')`. Both are join
homomorphisms between complete join semi-lattices, exactly the shape
captured by `Plurality.Algebra.Materialization` (= mathlib's
`SupHom I Q`). K89's specific bisorted I/Q framing adds the identity-
on-Q condition; the lattice-homomorphism backbone is shared. -/

section Materialization

variable {I Q : Type*} [SemilatticeSup I] [SemilatticeSup Q]

/-- K89's homomorphism law `h(x ∪ y) = h(x) ⊔ h(y)` (page 87) is the
    `map_sup'` clause of a `Materialization` (= `SupHom I Q`). This
    lemma exposes it as a named theorem for K89-side use; a
    join-homomorphism is constructed from any `IsSumHom`-bearing
    function via `IsSumHom.toSupHom` (e.g., for the temporal trace
    `τ : E → T` from §5 D40, page 96). -/
theorem materialization_join (mat : Materialization I Q) (x y : I) :
    mat (x ⊔ y) = mat x ⊔ mat y :=
  mat.map_sup' x y

end Materialization

/-- *Ann drank wine in 0.43 seconds* (K89 §5 eq. 19): a CUM-NP VP that
    accepts *in*-X. Listed as a thematic datum (K89 §4 eat-class) with
    the *wine* NP, flagged as the edge case where ATM and QUA come
    apart on the object NP. -/
def annDrankWineInSeconds : K89ThematicDatum :=
  { verb := .eat,  -- "drink" not in §4 verb list, eat is the consumed-patient sibling
    thematicClass := .gradualConsumedPatient,
    npDatum := wineNP }

/-- The wine NP in *Ann drank wine in 0.43 seconds* is CUM (mass noun).
    Without atomicity-not-quantization licensing (K89 §5), the §5
    *in*-X acceptance would be unexplained. -/
theorem ann_drank_wine_object_is_cum :
    annDrankWineInSeconds.npDatum.refType = .cum := rfl

/-- The §5 contrast partner: *drink a glass of wine in 0.43 seconds*'s
    object IS QUA (measure construction), so the K89 §3 D28 chain
    handles it via QMOD; the wine bare-mass case in
    `annDrankWineInSeconds` is the one that requires the ATM-not-QUA
    pathway formalized as `ATM` above. -/
theorem aGlassOfWine_is_qua :
    aGlassOfWineNP.refType = .qua := rfl

/-! ### Quantification (K89 §7) -/

/-! K89 §7 introduces:

    - definite NPs (eq. 35-36) via maximal-individual semantics;
    - increasing/decreasing quantifiers (eq. 31-34) via maximal events
      + the `max` function (D46);
    - cumulative readings (eq. 37-40) via summative thematic relations;
    - distributive readings (eq. 41-42) via the ATP atomic-part operator.

    This section registers the data items K89 builds his quantification
    analysis on. Full formalization of `max` / MXE / MXT / cumulative-
    distributive derivations is left to a successor file (e.g. a
    `Studies/Krifka1989Quant.lean`); the
    chronological anchor is here, but the substrate work-product would
    naturally cluster with Plurals/Quantification, where Champollion
    2017 already engages cumulative readings. -/

/-- The reading-type of a K89 §7 quantification datum, per the paper's
    eq. 31-32 (increasing/decreasing) and eq. 37/41-42 (cumulative,
    distributive). -/
inductive K89Reading where
  | increasingProportional   -- "most girls" (K89 eq. 31)
  | decreasing               -- "less than three girls" (K89 eq. 32)
  | cumulative               -- "two girls ate seven apples" (K89 eq. 37)
  | distributive             -- "two girls ate seven apples each" (K89 eq. 42)
  deriving DecidableEq, Repr

/-- Paper-internal reference for each K89 §7 reading. -/
def K89Reading.eqRef : K89Reading → String
  | .increasingProportional => "K89 §7 eq. 31"
  | .decreasing             => "K89 §7 eq. 32"
  | .cumulative             => "K89 §7 eq. 37"
  | .distributive           => "K89 §7 eq. 42"

/-- A K89 §7 quantification datum: the English sentence + reading kind.
    Does NOT carry an NPDatum (the proportional/decreasing-quantifier
    NPs are not §3 CUM/QUA-classified; K89 §7 treats them via
    maximal-event semantics instead). -/
structure K89QuantDatum where
  sentence : String
  reading : K89Reading
  deriving Repr

def mostGirlsSang : K89QuantDatum :=
  { sentence := "Most girls sang", reading := .increasingProportional }

def lessThanThreeGirlsSang : K89QuantDatum :=
  { sentence := "Less than three girls sang", reading := .decreasing }

def twoGirlsAteSevenApples : K89QuantDatum :=
  { sentence := "Two girls ate seven apples", reading := .cumulative }

def twoGirlsAteSevenApplesEach : K89QuantDatum :=
  { sentence := "Two girls ate seven apples each", reading := .distributive }

def k89Section7Data : List K89QuantDatum :=
  [mostGirlsSang, lessThanThreeGirlsSang, twoGirlsAteSevenApples, twoGirlsAteSevenApplesEach]

/-! ### Scope: predicate-level QUA/CUM ≠ carrier-level boundedness -/

/-! [krifka-1989] defines `QUA` and `CUM` (D 14, D 12, p. 78) as
    properties of *predicates* over a structured carrier — a complete
    join semilattice with a part relation. K89 makes no claim that these
    predicate-level properties entail bounds on the *carrier* itself
    (e.g. that it has Mathlib `OrderTop` / `OrderBot` instances).

    This matters because downstream linglib code uses
    `Core.Order.MereoTag.qua = .closed` as a lexical-classification tag
    that conflates the two levels. That conflation is convenient for
    cross-framework gluing across [krifka-1989], [kennedy-2007],
    [rouillard-2026] (see the mereological-dimension lemmas in
    `Semantics/Mereology.lean` for the structural facts that DO hold —
    e.g. `qua_pullback_mereoDim`, `cum_measure_unbounded`), but it does
    not follow from K89's definitions.
    The two examples below show the gap in both directions.

    The defeasible cross-domain bridge `closed scale → telic verb` for
    *degree achievements specifically* is [hay-kennedy-levin-1999]'s
    contribution (lengthen, cool, straighten); it is not K89's claim, and
    even HKL restrict it to verbs derived from gradable adjectives. -/

/-- **Forward gap**: a predicate can be K89-QUA on a carrier that has no
    `OrderTop` instance. The singleton predicate `(· = 5)` on `ℕ` is QUA
    (no proper part of 5 in ℕ also equals 5), but ℕ has no maximum. -/
example : Mereology.QUA (α := ℕ) (· = 5) := Mereology.singleton_qua 5

example : NoMaxOrder ℕ := inferInstance

/-- **Reverse gap**: a carrier can be order-bounded on both ends without
    its predicates being K89-QUA. `Fin 3` has both `OrderTop` and
    `OrderBot`, but the predicate "value is at most 1" admits both `0`
    and `1` with `0 < 1` — QUA's no-proper-part-overlap condition fails. -/
example : ¬ Mereology.QUA (α := Fin 3) (fun k => k.val ≤ 1) := by
  intro h
  have h1 : (1 : Fin 3).val ≤ 1 := by decide
  have h0 : (0 : Fin 3).val ≤ 1 := by decide
  have hlt : (0 : Fin 3) < 1 := by decide
  exact h h0 h1 hlt.ne hlt.le

example : OrderTop (Fin 3) := inferInstance
example : OrderBot (Fin 3) := inferInstance

end Krifka1989
