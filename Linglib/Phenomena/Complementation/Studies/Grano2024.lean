import Linglib.Theories.Semantics.Mood.Basic
import Linglib.Theories.Semantics.Attitudes.RationalAttitude
import Linglib.Phenomena.Complementation.Studies.Noonan2007
import Linglib.Fragments.Greek.MoodChoice
import Linglib.Fragments.Romanian.MoodChoice
import Linglib.Fragments.Spanish.MoodChoice
import Linglib.Fragments.Portuguese.MoodChoice

/-!
# Grano 2024: Intention Reports and Eventuality Abstraction @cite{grano-2024}

Cross-linguistic mood choice data and bridge theorems connecting
@cite{grano-2024}'s analysis of intention reports to the mood and
attitude infrastructure.

## Core Proposal (three premises → conclusion)

1. **Premise 1**: Intention reports encode causally self-referential content
   (@cite{searle-1983}; Harman 1976)
2. **Premise 2**: Encoding causal self-reference requires abstraction over
   the complement clause's eventuality argument (CAUSE* binds it)
3. **Premise 3**: Only subjunctive and nonfinite clauses enable eventuality
   abstraction; indicative clauses existentially close the event argument
4. **Conclusion**: 'intend' accepts subjunctive/nonfinite but rejects
   indicative complements cross-linguistically

## Table 1: Cross-Linguistic Mood Choice

The central empirical finding: 'intend' patterns with 'want' (not 'hope')
in robustly rejecting indicative complements. 'hope' exhibits cross-linguistic
and language-internal variation; 'intend' does not.

Independent support comes from causative predicates ('make'), intention-rigid
predicates ('aim', 'try'), belief–intention hybrid predicates ('decide',
'convince'), aspectual predicates ('begin'), and memory/perception reports
('remember', 'see'). All pattern alike: subjunctive/nonfinite required,
indicative rejected.

## Unified Theory (§7)

Subjunctive mood uniformly signals a departure from the default clausal
semantics of unembedded assertions. Two kinds of departure:
- **Comparison** (ordering semantics): 'want', 'hope' (@cite{portner-rubinstein-2020})
- **Eventuality abstraction**: 'intend', causatives, aspectuals (this paper)

When neither departure is present, only indicative mood is possible.
-/

namespace Phenomena.Complementation.Studies.Grano2024

open Semantics.Mood
open Semantics.Attitudes.RationalAttitude

-- ════════════════════════════════════════════════════════════════
-- § 1. Cross-Linguistic Mood Choice Data (Table 1)
-- ════════════════════════════════════════════════════════════════

/-- A mood choice observation: whether a predicate in a language
    rejects indicative complements (@cite{grano-2024}, Table 1).

    This is the key variable: 'want' and 'intend' robustly reject IND
    across languages, while 'hope' does not. -/
structure MoodChoiceDatum where
  language : String
  predicate : String
  rejectsIndicative : Bool
  deriving DecidableEq, BEq, Repr

-- ── 'want': robustly rejects IND across all 7 languages ──

def spanish_want  := MoodChoiceDatum.mk "Spanish"    "querer"  true
def french_want   := MoodChoiceDatum.mk "French"     "vouloir" true
def portuguese_want := MoodChoiceDatum.mk "Portuguese" "querer" true
def italian_want  := MoodChoiceDatum.mk "Italian"    "volere"  true
def greek_want    := MoodChoiceDatum.mk "Greek"      "thélo"   true
def romanian_want := MoodChoiceDatum.mk "Romanian"   "a vrea"  true
def english_want  := MoodChoiceDatum.mk "English"    "want"    true

-- ── 'hope': cross-linguistically variable ──
-- Spanish: SBJV only (ex. 9)
-- French: IND preferred, %SBJV for some speakers (ex. 10)
-- Portuguese: IND/SBJV (ex. 11)
-- Italian: SBJV preferred, %IND marginal (ex. 12)
-- Greek: IND/SBJV via na/oti complementizer (ex. 13)
-- Romanian: IND/SBJV (ex. 14)
-- English: IND and for-to (ex. 15–16)

def spanish_hope    := MoodChoiceDatum.mk "Spanish"    "esperar"  true
def french_hope     := MoodChoiceDatum.mk "French"     "espérer"  false
def portuguese_hope := MoodChoiceDatum.mk "Portuguese" "esperar"  false
def italian_hope    := MoodChoiceDatum.mk "Italian"    "sperare"  false
def greek_hope      := MoodChoiceDatum.mk "Greek"      "elpízo"   false
def romanian_hope   := MoodChoiceDatum.mk "Romanian"   "a spera"  false
def english_hope    := MoodChoiceDatum.mk "English"    "hope"     false

-- ── 'intend': robustly rejects IND (like 'want') ──
-- Greek: na/*oti (ex. 22)
-- Romanian: să/*că (ex. 23)
-- Spanish: SBJV in non-control complements (ex. 25)
-- Portuguese: SBJV (ex. 26)
-- English: for-to only; *that-clause (ex. 21, 24)

def spanish_intend    := MoodChoiceDatum.mk "Spanish"    "tener la intención" true
def portuguese_intend := MoodChoiceDatum.mk "Portuguese" "pretender"          true
def greek_intend      := MoodChoiceDatum.mk "Greek"      "protíthete"         true
def romanian_intend   := MoodChoiceDatum.mk "Romanian"   "a intenționa"       true
def english_intend    := MoodChoiceDatum.mk "English"    "intend"             true

-- ── Causatives: also robustly reject IND (§2.4) ──

def spanish_make  := MoodChoiceDatum.mk "Spanish"    "hacer"  true
def french_make   := MoodChoiceDatum.mk "French"     "faire"  true
def portuguese_make := MoodChoiceDatum.mk "Portuguese" "fazer" true
def italian_make  := MoodChoiceDatum.mk "Italian"    "fare"   true
def greek_make    := MoodChoiceDatum.mk "Greek"      "vázo"   true
def romanian_make := MoodChoiceDatum.mk "Romanian"   "a face" true
def english_make  := MoodChoiceDatum.mk "English"    "make"   true

-- ════════════════════════════════════════════════════════════════
-- § 2. Data Collections and Generalizations
-- ════════════════════════════════════════════════════════════════

def wantData : List MoodChoiceDatum :=
  [spanish_want, french_want, portuguese_want, italian_want,
   greek_want, romanian_want, english_want]

def hopeData : List MoodChoiceDatum :=
  [spanish_hope, french_hope, portuguese_hope, italian_hope,
   greek_hope, romanian_hope, english_hope]

def intendData : List MoodChoiceDatum :=
  [spanish_intend, portuguese_intend, greek_intend,
   romanian_intend, english_intend]

def causativeData : List MoodChoiceDatum :=
  [spanish_make, french_make, portuguese_make, italian_make,
   greek_make, romanian_make, english_make]

/-- 'want' robustly rejects indicative across all 7 languages. -/
theorem want_robustly_rejects_ind :
    wantData.all (·.rejectsIndicative) = true := by native_decide

/-- 'hope' does NOT robustly reject indicative — it varies
    (IND accepted in French, Portuguese, Italian, Greek, Romanian, English). -/
theorem hope_does_not_robustly_reject_ind :
    hopeData.all (·.rejectsIndicative) = false := by native_decide

/-- 'intend' robustly rejects indicative (where testable). -/
theorem intend_robustly_rejects_ind :
    intendData.all (·.rejectsIndicative) = true := by native_decide

/-- Causatives robustly reject indicative (§2.4). -/
theorem causatives_robustly_reject_ind :
    causativeData.all (·.rejectsIndicative) = true := by native_decide

/-- 'intend' patterns with 'want', not 'hope', on indicative rejection.
    This is the central empirical finding (@cite{grano-2024}, Table 1). -/
theorem intend_patterns_with_want :
    intendData.all (·.rejectsIndicative) =
      wantData.all (·.rejectsIndicative) ∧
    intendData.all (·.rejectsIndicative) ≠
      hopeData.all (·.rejectsIndicative) := by
  native_decide

/-- Causatives pattern with 'intend' and 'want' (not 'hope').
    Independent support for the eventuality abstraction analysis (§2.4). -/
theorem causatives_pattern_with_intend :
    causativeData.all (·.rejectsIndicative) =
      intendData.all (·.rejectsIndicative) := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- § 3. Bridge: Empirical Data → MoodSelector
-- ════════════════════════════════════════════════════════════════

open Phenomena.Complementation.Bridge (deriveMoodSelector)
open Fragments.English.Predicates.Verbal (want hope)

/-- The deriveMoodSelector function correctly classifies 'want' as
    robustly subjunctive-selecting, matching the cross-linguistic data. -/
theorem want_selector_matches_data :
    deriveMoodSelector want = .subjunctiveSelecting ∧
    wantData.all (·.rejectsIndicative) = true := by
  native_decide

/-- The deriveMoodSelector function correctly classifies 'hope' as
    cross-linguistically variable, matching the data showing variation. -/
theorem hope_selector_matches_data :
    deriveMoodSelector hope = .crossLinguisticallyVariable ∧
    hopeData.all (·.rejectsIndicative) = false := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- § 4. Bridge: MoodEffect → Indicative Rejection
-- ════════════════════════════════════════════════════════════════

/-- Indicative mood closes the eventuality argument. Therefore,
    predicates requiring eventuality abstraction (CAUSE* binds the
    event variable) reject indicative complements.

    This is the formal correlate of @cite{grano-2024}'s argument chain:
    Premise 2 (CAUSE* needs open event arg) + Premise 3 (IND closes it)
    → Conclusion (intention reports reject IND). -/
theorem ind_incompatible_with_eventuality_abstraction :
    GramMood.indicative.effect.eventualityOpen = false := rfl

/-- Subjunctive mood leaves the eventuality argument open, enabling
    CAUSE* to bind it. This is why 'intend' and causatives accept SBJV. -/
theorem subj_enables_eventuality_abstraction :
    GramMood.subjunctive.effect.eventualityOpen = true := rfl

/-- The three-premise argument chain:
    1. `intentionHolds` requires P : E → W → Ev Time → Prop (open event arg)
    2. IND closes the event argument (eventualityOpen = false)
    3. SBJV leaves it open (eventualityOpen = true)
    → intention reports require SBJV, reject IND -/
theorem grano_argument_chain :
    -- Premise 3: IND closes, SBJV opens
    GramMood.indicative.effect.eventualityOpen = false ∧
    GramMood.subjunctive.effect.eventualityOpen = true ∧
    -- Empirical confirmation: intend rejects IND
    intendData.all (·.rejectsIndicative) = true ∧
    -- Empirical confirmation: causatives also reject IND (independent support)
    causativeData.all (·.rejectsIndicative) = true := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════════════════
-- § 5. Bridge: Unified Theory — Two Kinds of Departure
-- ════════════════════════════════════════════════════════════════

/-- @cite{grano-2024} §7 proposes that subjunctive mood uniformly signals
    a departure from the default clausal semantics of unembedded assertions.
    Two kinds of departure trigger SBJV:
    - **Comparison**: ordering semantics with two modal backgrounds
      (want, hope; @cite{portner-rubinstein-2020})
    - **Eventuality abstraction**: open event argument for CAUSE* or
      aspect (intend, causatives, aspectuals; this paper)

    Predicates like 'hope' involve comparison only (variable mood).
    Predicates like 'want' involve comparison (robust SBJV: simplification
      blocked because 'want' does not allow inconsistent prejacents).
    Predicates like 'intend' involve both comparison and eventuality
      abstraction (robust SBJV: IND is type-incompatible with CAUSE*).
    Predicates like 'believe' involve neither → indicative only. -/
inductive DepartureKind where
  | comparisonSimplifiable    -- ordering semantics, modal backgrounds can simplify
                              -- to one → IND possible in some languages ('hope')
  | comparisonNonSimplifiable -- ordering semantics, simplification blocked because
                              -- 'want' tolerates inconsistent prejacents ((50), (60))
                              -- → both modal backgrounds must remain → robust SBJV
  | eventualityAbstraction    -- open event argument ('begin', 'make')
  | comparisonAndAbstraction  -- comparison + eventuality abstraction ('intend')
  deriving DecidableEq, BEq, Repr

/-- Map departure kind to mood selection prediction.

    @cite{grano-2024} §7: both comparison and eventuality abstraction
    are departures from the default clausal semantics that trigger SBJV.
    The key empirical difference:

    - **Comparison alone**: SBJV is expected, but Portner & Rubinstein's
      simplification of two modal backgrounds into one can license IND
      in some languages (French *espérer*). This yields cross-linguistic
      variation for 'hope'-type verbs.
    - **Eventuality abstraction** (± comparison): SBJV is robust because
      IND existentially closes the event argument, making it
      type-incompatible with CAUSE* / aspect / perception. No
      simplification can rescue IND here. -/
def DepartureKind.moodPrediction : DepartureKind → MoodSelector
  | .comparisonSimplifiable    => .crossLinguisticallyVariable
  | .comparisonNonSimplifiable => .subjunctiveSelecting
  | .eventualityAbstraction    => .subjunctiveSelecting
  | .comparisonAndAbstraction  => .subjunctiveSelecting

/-- Eventuality abstraction robustly predicts subjunctive selection
    (IND is type-incompatible with open event argument). -/
theorem eventuality_abstraction_robust :
    DepartureKind.eventualityAbstraction.moodPrediction = .subjunctiveSelecting ∧
    DepartureKind.comparisonAndAbstraction.moodPrediction = .subjunctiveSelecting :=
  ⟨rfl, rfl⟩

/-- Simplifiable comparison allows cross-linguistic variation (the 'hope' pattern).
    Per @cite{portner-rubinstein-2020}: when two modal backgrounds can
    simplify to one, IND becomes available. -/
theorem simplifiable_comparison_variable :
    DepartureKind.comparisonSimplifiable.moodPrediction =
      .crossLinguisticallyVariable := rfl

/-- Non-simplifiable comparison robustly predicts SBJV (the 'want' pattern).
    'want' blocks simplification: it does not tolerate inconsistent
    prejacents ((50), (60)), so both modal backgrounds must remain. -/
theorem nonsimplifiable_comparison_robust :
    DepartureKind.comparisonNonSimplifiable.moodPrediction =
      .subjunctiveSelecting := rfl

/-- 'intend' (comparison + abstraction) patterns with 'want' (non-simplifiable
    comparison), not with 'hope' (simplifiable comparison). This is the central
    prediction: all three involve comparison, but eventuality abstraction
    independently blocks IND. -/
theorem intend_patterns_with_want_not_hope :
    DepartureKind.comparisonAndAbstraction.moodPrediction =
      DepartureKind.comparisonNonSimplifiable.moodPrediction ∧
    DepartureKind.comparisonAndAbstraction.moodPrediction ≠
      DepartureKind.comparisonSimplifiable.moodPrediction := by
  decide

-- ════════════════════════════════════════════════════════════════
-- § 6. Independent Support (§6)
-- ════════════════════════════════════════════════════════════════

/-! ### §6.1 Intention-Rigid Predicates

Predicates that obligatorily encode intention: aim, try, endeavor, strive,
seek. All share 'intend's causally self-referential, goal-oriented property
and, as predicted, reject indicative complements ((90)–(91)).

### §6.2 Belief-Intention Hybrid Predicates

Predicates like 'decide', 'convince', 'persuade' report either belief or
intention formation depending on complement type ((96)–(97)):
- Nonfinite complement → intention reading → requires SBJV/nonfinite
- Finite complement → belief reading → allows IND

This is exactly the complement-size-driven alternation that
@cite{fusco-sgrizzi-2026} formalizes for Italian *convincere*.

### §6.3 Aspectual Predicates

Aspect is inherently event-related and requires eventuality abstraction.
Aspectual predicates (begin, start, stop, continue) accept nonfinite/SBJV
complements but reject finite indicative complements ((115)–(119)).

### §6.4 Memory and Perception Reports

'remember' + gerund = event construal (eventuality abstraction);
'remember' + *that*-clause = propositional construal (no abstraction).
'see' + bare infinitive = event perception;
'see' + *that*-clause = indirect evidence. ((120)–(127))
-/

open Fragments.English.Predicates.Verbal (intend try_ persuade promise decide_
    start stop begin_ continue_ see remember)

/-- Intention-rigid predicates reject IND like 'intend' (§6.1, (91)).
    'try' is in the English fragment; it takes infinitival complements
    and has no alternate finite complement type. -/
theorem try_rejects_finite :
    try_.complementType = .infinitival ∧
    try_.altComplementType = none := by native_decide

/-- 'persuade' is a hybrid predicate: nonfinite complement with object
    control → intention reading. This matches @cite{grano-2024} §6.2 (96). -/
theorem persuade_is_hybrid :
    persuade.complementType = .infinitival ∧
    persuade.controlType = .objectControl := by native_decide

/-- 'promise' is a hybrid predicate: nonfinite complement with subject
    control → intention (commissive). Matches §6.2 (98a). -/
theorem promise_is_hybrid :
    promise.complementType = .infinitival ∧
    promise.controlType = .subjectControl := by native_decide

/-- Aspectual predicates are phasal (cosType.isSome) and take gerund
    complements in English, consistent with requiring eventuality
    abstraction (§6.3, (115)–(116)). In Romance, these take infinitival
    or subjunctive complements ((117)–(119)). -/
theorem start_is_phasal :
    start.cosType.isSome = true ∧
    start.complementType = .gerund := by native_decide

theorem stop_is_phasal :
    stop.cosType.isSome = true ∧
    stop.complementType = .gerund := by native_decide

theorem begin_is_phasal :
    begin_.cosType.isSome = true ∧
    begin_.complementType = .gerund := by native_decide

theorem continue_is_phasal :
    continue_.cosType.isSome = true ∧
    continue_.complementType = .gerund := by native_decide

/-- 'see' takes NP complements primarily (bare perception), with
    factive presupposition. The bare infinitive (eventive, §6.4 (124))
    vs *that*-clause (propositional, §6.4 (125)) alternation tracks
    eventuality abstraction. -/
theorem see_is_factive_perception :
    see.factivePresup = true ∧
    see.levinClass = some .see := by native_decide

/-- 'decide' is a hybrid predicate: nonfinite complement → intention,
    finite complement → belief (@cite{grano-2024} §6.2, (96)–(97)).
    Like 'persuade' and 'convince', the complement type determines whether
    the reading is intentional or propositional. -/
theorem decide_is_hybrid :
    decide_.complementType = .infinitival ∧
    decide_.altComplementType = some .finiteClause ∧
    decide_.controlType = .subjectControl := by native_decide

/-- 'remember' takes infinitival (implicative/eventive, §6.4 (120)).
    The gerund construal enables event memory; the *that*-clause
    enables propositional memory ((120)–(121)). -/
theorem remember_is_implicative :
    remember.complementType = .infinitival ∧
    remember.implicativeBuilder.isSome = true := by native_decide

-- ════════════════════════════════════════════════════════════════
-- § 7. Bridge: Fusco & Sgrizzi 2026 Connection
-- ════════════════════════════════════════════════════════════════

/-! ### Complement Size → Reading → Mood

@cite{grano-2024}'s hybrid predicate analysis (§6.2) and
@cite{fusco-sgrizzi-2026}'s complement-size analysis make the same
prediction: the complement's structural size determines whether the
reading is intentional (requiring eventuality abstraction → SBJV) or
propositional (existentially closed → IND-compatible).

The connection: Fusco & Sgrizzi's `readingFromSize` maps complement
sizes to readings; Grano's `DepartureKind` maps readings to mood
predictions. Together they form an end-to-end chain:

    complement size → reading → departure kind → mood prediction
-/

/-- Map a rational attitude reading to a departure kind.

    Intention readings require eventuality abstraction (CAUSE* binds the
    event argument). Belief readings involve neither comparison nor
    eventuality abstraction — they are the default clausal semantics. -/
def readingToDeparture : Reading → Option DepartureKind
  | .intention => some .eventualityAbstraction
  | .belief    => none  -- no departure from default

/-- Intention readings predict robust subjunctive selection. -/
theorem intention_predicts_subjunctive :
    (readingToDeparture .intention).map DepartureKind.moodPrediction =
      some .subjunctiveSelecting := rfl

/-- Belief readings predict no departure (default = indicative). -/
theorem belief_predicts_no_departure :
    readingToDeparture .belief = none := rfl

/-- End-to-end: sub-CP complement → intention → eventuality abstraction
    → robust subjunctive selection. -/
theorem subcp_to_subjunctive :
    let reading := readingFromSize .vP                -- sub-CP → intention
    let departure := readingToDeparture reading       -- intention → ev. abstraction
    let mood := departure.map DepartureKind.moodPrediction
    reading = .intention ∧
    departure = some .eventualityAbstraction ∧
    mood = some .subjunctiveSelecting := ⟨rfl, rfl, rfl⟩

/-- End-to-end: CP complement → belief → no departure → no SBJV
    requirement (default = indicative). -/
theorem cp_to_indicative :
    let reading := readingFromSize .cP                -- CP → belief
    let departure := readingToDeparture reading       -- belief → no departure
    reading = .belief ∧
    departure = none := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 8. Predicate Classification by Departure Kind
-- ════════════════════════════════════════════════════════════════

-- Per-predicate departure classifications. These are stated directly
-- rather than computed from VerbEntry fields because the crucial
-- distinction — whether a predicate has a causative component (CAUSE*)
-- — is not yet captured by a VerbEntry field. The classifications are
-- verified to agree with the independently derived `deriveMoodSelector`.

/-- 'want' involves non-simplifiable comparison (robust SBJV). -/
theorem want_moodPrediction_agrees :
    DepartureKind.comparisonNonSimplifiable.moodPrediction =
      deriveMoodSelector want := by native_decide

/-- 'hope' involves simplifiable comparison (variable mood). -/
theorem hope_moodPrediction_agrees :
    DepartureKind.comparisonSimplifiable.moodPrediction =
      deriveMoodSelector hope := by native_decide

/-- 'intend' involves both comparison and eventuality abstraction
    (robust SBJV). -/
theorem intend_moodPrediction_agrees :
    DepartureKind.comparisonAndAbstraction.moodPrediction =
      deriveMoodSelector intend := by native_decide

/-- Causatives involve eventuality abstraction (robust SBJV). -/
theorem causative_moodPrediction_agrees :
    DepartureKind.eventualityAbstraction.moodPrediction =
      deriveMoodSelector Fragments.English.Predicates.Verbal.make := by native_decide

-- ════════════════════════════════════════════════════════════════
-- § 9. Cross-Linguistic Fragment Integration
-- ════════════════════════════════════════════════════════════════

/-! ### Fragment Entry ↔ Datum Consistency

The cross-linguistic fragment files encode verb properties that should be
consistent with the mood choice data. For predicates in the want-class
(levinClass = .want), the datum should have rejectsIndicative = true.
For predicates NOT in the want-class (like 'hope'), the mood variability
is captured by deriveMoodSelector returning .crossLinguisticallyVariable. -/

-- Greek fragments match Greek data
theorem greek_want_fragment_consistent :
    Fragments.Greek.MoodChoice.thelo.levinClass = some LevinClass.want ∧
    greek_want.rejectsIndicative = true := ⟨rfl, rfl⟩

theorem greek_hope_fragment_consistent :
    Fragments.Greek.MoodChoice.elpizo.levinClass ≠ some LevinClass.want ∧
    greek_hope.rejectsIndicative = false := ⟨by decide, rfl⟩

theorem greek_intend_fragment_consistent :
    Fragments.Greek.MoodChoice.protithete.levinClass = some LevinClass.want ∧
    greek_intend.rejectsIndicative = true := ⟨rfl, rfl⟩

theorem greek_make_fragment_consistent :
    Fragments.Greek.MoodChoice.vazo.causativeBuilder.isSome = true ∧
    greek_make.rejectsIndicative = true := ⟨rfl, rfl⟩

-- Romanian fragments match Romanian data
theorem romanian_want_fragment_consistent :
    Fragments.Romanian.MoodChoice.a_vrea.levinClass = some LevinClass.want ∧
    romanian_want.rejectsIndicative = true := ⟨rfl, rfl⟩

theorem romanian_hope_fragment_consistent :
    Fragments.Romanian.MoodChoice.a_spera.levinClass ≠ some LevinClass.want ∧
    romanian_hope.rejectsIndicative = false := ⟨by decide, rfl⟩

theorem romanian_intend_fragment_consistent :
    Fragments.Romanian.MoodChoice.a_intentiona.levinClass = some LevinClass.want ∧
    romanian_intend.rejectsIndicative = true := ⟨rfl, rfl⟩

-- Spanish fragments match Spanish data
theorem spanish_want_fragment_consistent :
    Fragments.Spanish.MoodChoice.querer.levinClass = some LevinClass.want ∧
    spanish_want.rejectsIndicative = true := ⟨rfl, rfl⟩

theorem spanish_intend_fragment_consistent :
    Fragments.Spanish.MoodChoice.tener_la_intencion.levinClass = some LevinClass.want ∧
    spanish_intend.rejectsIndicative = true := ⟨rfl, rfl⟩

-- Portuguese fragments match Portuguese data
theorem portuguese_want_fragment_consistent :
    Fragments.Portuguese.MoodChoice.querer.levinClass = some LevinClass.want ∧
    portuguese_want.rejectsIndicative = true := ⟨rfl, rfl⟩

theorem portuguese_intend_fragment_consistent :
    Fragments.Portuguese.MoodChoice.pretender.levinClass = some LevinClass.want ∧
    portuguese_intend.rejectsIndicative = true := ⟨rfl, rfl⟩

end Phenomena.Complementation.Studies.Grano2024
