import Linglib.Theories.Semantics.Tense.Basic
import Linglib.Core.Time.Tense

/-!
# @cite{wurmbrand-2014}: Tense and Aspect in English Infinitives
@cite{wurmbrand-2014}

Wurmbrand's three-way classification of infinitival complements by tense
properties. The key insight: infinitival complements are not uniformly
"tenseless" — they fall into three classes with distinct temporal behavior.

## Core Mechanisms

1. **Three-way classification**: future irrealis, propositional, tenseless simultaneous
2. **Woll decomposition**: *will* = PRES + *woll*; *would* = PAST + *woll*
3. **Temporal orientation** is determined by complement class, not tense morphology
4. **Dependent vs independent tense**: restructuring complements share the
   matrix temporal domain; propositional complements have NOW-anchoring
5. **Episodic interpretation diagnostics**: the three classes make distinct
   predictions about whether bare (nonprogressive) episodic VPs are possible
6. **Complement size**: infinitival tense class correlates with complement size
   (wollP, TP, or vP/AspP)

## Classification (Table 4)

| Class                      | Example verbs      | Temporal composition       | Complement size |
|----------------------------|--------------------|----------------------------|-----------------|
| Irrealis future            | decide, expect     | *woll* (future modal)      | wollP           |
| Propositional              | believe, claim     | Ref time = att. holder NOW | TP              |
| Nonpropositional (no att.) | try, begin, seem   | Ref time = matrix ref time | vP/AspP         |

## Episodic Interpretations (Table 3)

| Class                    | Episodic interp. | Reason                           |
|--------------------------|------------------|----------------------------------|
| Future                   | possible         | woll gives unrestricted ref time |
| Propositional attitude   | impossible       | NOW = short interval, perf fails |
| Tenseless simultaneous   | matrix-dependent | ref time = matrix ref time       |

## Limitations

- Focuses on English infinitives; cross-linguistic extension is programmatic
- Temporal de re: not directly addressed
- ULC: not directly addressed

-/

namespace Minimalism.Tense.InfinitivalTense

open Core.Time.Tense
open Core.Time.Reichenbach
open Semantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § 1: Infinitival Tense Classification
-- ════════════════════════════════════════════════════════════════

/-- @cite{wurmbrand-2014}'s three-way classification of infinitival tense.

    The paper's final characterization (Table 4):
    - **Irrealis future**: tenseless + *woll* → future-oriented
    - **Propositional**: reference time = attitude holder's NOW → simultaneous
    - **Tenseless simultaneous**: no attitude holder, reference time =
      matrix reference time → dependent on matrix

    The third class is labeled "Nonpropositional; no attitude holder" in
    Table 4 and subsumes both restructuring verbs (*try*, *manage*) and
    raising verbs (*begin*, *seem*). -/
inductive InfinitivalTenseClass where
  /-- decide, want, expect: tenseless + woll → future-oriented -/
  | futureIrrealis
  /-- believe, claim, expect: NOW-anchored → simultaneous with attitude time -/
  | propositional
  /-- try, begin, manage, seem: no attitude holder, reference time =
      matrix reference time → dependent on matrix.
      Labeled "Nonpropositional; no attitude holder" in Table 4.
      Subsumes both restructuring and raising infinitives. -/
  | restructuring
  deriving DecidableEq, Repr, Inhabited


-- ════════════════════════════════════════════════════════════════
-- § 2: Complement Size
-- ════════════════════════════════════════════════════════════════

/-- Complement size hierarchy (@cite{wurmbrand-2014} §5; @cite{wurmbrand-2001}).

    The three infinitival classes correspond to different complement
    sizes in the clausal spine. The functional domain is built uniformly
    from the bottom up; restructuring is special only in that the
    functional domain is not built up to the top. Higher projections
    entail lower ones — a wollP cannot exist without a vP below it. -/
inductive ComplementSize where
  /-- wollP: contains the future modal *woll*. Entails vP below.
      Selected by future-irrealis verbs (*decide*, *plan*, *promise*). -/
  | wollP
  /-- TP: contains a tense head anchored to attitude holder's NOW.
      Selected by propositional attitude verbs (*believe*, *claim*). -/
  | tP
  /-- vP/AspP: bare aspectual projection, no independent tense or modal.
      Selected by restructuring/raising verbs (*try*, *begin*, *seem*). -/
  | vP_AspP
  deriving DecidableEq, Repr

/-- Map each infinitival tense class to its predicted complement size. -/
def classToSize : InfinitivalTenseClass → ComplementSize
  | .futureIrrealis => .wollP
  | .propositional => .tP
  | .restructuring => .vP_AspP

/-- Complement size ordering: larger complements properly contain
    smaller ones. wollP > TP > vP/AspP. -/
def ComplementSize.isLargerThan : ComplementSize → ComplementSize → Bool
  | .wollP, .tP => true
  | .wollP, .vP_AspP => true
  | .tP, .vP_AspP => true
  | _, _ => false


-- ════════════════════════════════════════════════════════════════
-- § 3: Woll Decomposition
-- ════════════════════════════════════════════════════════════════

/-- Woll: abstract future modal (@cite{wurmbrand-2014} §2).
    *will* = PRES + *woll*; *would* = PAST + *woll*.

    This decomposes English future auxiliaries into a tense component
    and a modal component (woll). The tense component is what undergoes
    SOT; woll provides the future orientation. -/
structure WollDecomposition where
  /-- The tense component -/
  tense : GramTense
  /-- Whether woll is present (provides future orientation) -/
  hasWoll : Bool
  deriving DecidableEq, Repr

/-- *will* = present tense + woll. -/
def will_ : WollDecomposition where
  tense := .present
  hasWoll := true

/-- *would* = past tense + woll. -/
def would_ : WollDecomposition where
  tense := .past
  hasWoll := true

/-- Plain present (no woll). -/
def plainPresent : WollDecomposition where
  tense := .present
  hasWoll := false

/-- *will* and *would* share the woll component. -/
theorem will_would_share_woll :
    will_.hasWoll = would_.hasWoll := rfl

/-- *will* and *would* differ only in tense. -/
theorem will_would_tense_differs :
    will_.tense ≠ would_.tense := nofun

/-- Whether a class's complement contains woll. Only future irrealis
    infinitives contain the future modal *woll*; the other two classes
    lack it. -/
def classHasWoll : InfinitivalTenseClass → Bool
  | .futureIrrealis => true
  | .propositional => false
  | .restructuring => false

/-- Future irrealis infinitives contain woll. -/
theorem futureIrrealis_has_woll :
    classHasWoll .futureIrrealis = true := rfl

/-- Non-future classes lack woll. -/
theorem propositional_no_woll :
    classHasWoll .propositional = false := rfl

theorem restructuring_no_woll :
    classHasWoll .restructuring = false := rfl


-- ════════════════════════════════════════════════════════════════
-- § 4: Temporal Orientation by Class
-- ════════════════════════════════════════════════════════════════

/-- The temporal orientation of a complement relative to the matrix event.
    @cite{wurmbrand-2014}'s classification predicts distinct temporal
    relations for each class. -/
inductive TemporalOrientation where
  /-- Complement event is after matrix event -/
  | futureOriented
  /-- Complement event is simultaneous with matrix event -/
  | simultaneous
  /-- Complement event's temporal location depends entirely on matrix -/
  | dependent
  deriving DecidableEq, Repr

/-- Map each infinitival tense class to its predicted temporal orientation. -/
def classOrientation : InfinitivalTenseClass → TemporalOrientation
  | .futureIrrealis => .futureOriented
  | .propositional => .simultaneous
  | .restructuring => .dependent


-- ════════════════════════════════════════════════════════════════
-- § 5: Episodic Interpretation Predictions (Table 3)
-- ════════════════════════════════════════════════════════════════

/-- Availability of bare (nonprogressive) episodic interpretations
    in infinitival complements (@cite{wurmbrand-2014} §4).

    The three infinitival classes make distinct predictions about
    episodic VPs. Episodic interpretations require perfective aspect,
    which requires the event time to be *included in* the reference
    time interval. The three classes impose different reference time
    constraints, yielding different episodic patterns. -/
inductive EpisodicAvailability where
  /-- Episodic interpretations are possible because *woll* provides
      an unrestricted future reference time (large enough for perfective).
      Example: "John decided to sing in the shower" — episodic OK. -/
  | possible
  /-- Episodic interpretations are impossible because the reference time
      is the attitude holder's NOW — a near-instantaneous interval too
      short for perfective aspect to be satisfied.
      Example: "*Leo believes Julia to sing in the shower right now." -/
  | impossible
  /-- Episodic interpretations depend on the matrix tense: possible
      when the matrix reference time is large enough (past tense), but
      not when it is restricted to a short interval (present tense).
      Example: "Leo seemed to sing in the shower yesterday" — OK with
      past matrix; "*Leo seems to sing in the shower right now" — bad. -/
  | matrixDependent
  deriving DecidableEq, Repr

/-- Map each infinitival tense class to its episodic interpretation
    prediction (Table 3, p.432). -/
def classEpisodicPrediction : InfinitivalTenseClass → EpisodicAvailability
  | .futureIrrealis => .possible
  | .propositional => .impossible
  | .restructuring => .matrixDependent

/-- Propositional infinitives exclude bare episodic interpretations:
    the reference time (attitude holder's NOW) is too short for
    perfective aspect. Only imperfective/progressive is possible. -/
theorem propositional_no_episodic :
    classEpisodicPrediction .propositional = .impossible := rfl

/-- Restructuring infinitives' episodic availability is determined by
    the matrix tense (their reference time IS the matrix reference time):
    past matrix → large reference time → perfective OK → episodic OK;
    present matrix → short reference time → perfective fails → episodic bad. -/
theorem restructuring_episodic_matrix_dependent :
    classEpisodicPrediction .restructuring = .matrixDependent := rfl

/-- Future infinitives allow episodic interpretations regardless of
    matrix tense, because *woll* shifts the reference time to the
    future (an unrestricted interval). -/
theorem futureIrrealis_episodic_possible :
    classEpisodicPrediction .futureIrrealis = .possible := rfl


-- ════════════════════════════════════════════════════════════════
-- § 6: Example Verb Classifications
-- ════════════════════════════════════════════════════════════════

/-- Classification of infinitival complement verbs. -/
structure InfinitivalVerb where
  /-- The verb lemma -/
  lemma_ : String
  /-- Its tense class -/
  tenseClass : InfinitivalTenseClass
  deriving Repr

-- Future irrealis verbs
/-- "want" is future irrealis: "John wanted to leave" → leaving after wanting. -/
def want : InfinitivalVerb := ⟨"want", .futureIrrealis⟩

/-- "decide" is future irrealis: "John decided to leave" → leaving after deciding. -/
def decide : InfinitivalVerb := ⟨"decide", .futureIrrealis⟩

/-- "plan" is future irrealis: "John planned to leave" → leaving after planning. -/
def plan : InfinitivalVerb := ⟨"plan", .futureIrrealis⟩

/-- "promise" is future irrealis: "John promised to leave" → leaving after promising. -/
def promise : InfinitivalVerb := ⟨"promise", .futureIrrealis⟩

-- Propositional verbs
/-- "believe" is propositional: "John believes Mary to be sick" → simultaneous. -/
def believe : InfinitivalVerb := ⟨"believe", .propositional⟩

/-- "claim" is propositional: "John claims to be sick" → simultaneous. -/
def claim : InfinitivalVerb := ⟨"claim", .propositional⟩

-- Tenseless simultaneous (restructuring / raising) verbs
/-- "try" is tenseless simultaneous (restructuring): "John tried to leave" → same temporal domain. -/
def try_ : InfinitivalVerb := ⟨"try", .restructuring⟩

/-- "begin" is tenseless simultaneous (raising): "John began to sing" → same temporal domain. -/
def begin_ : InfinitivalVerb := ⟨"begin", .restructuring⟩

/-- "manage" is tenseless simultaneous (restructuring): "John managed to escape" → same temporal domain. -/
def manage : InfinitivalVerb := ⟨"manage", .restructuring⟩


-- ════════════════════════════════════════════════════════════════
-- § 7: Ambiguous Verbs
-- ════════════════════════════════════════════════════════════════

/-- A verb that is ambiguous between two infinitival tense classes.
    Some verbs allow multiple temporal construals depending on context. -/
structure AmbiguousVerb where
  lemma_ : String
  readings : List InfinitivalTenseClass
  deriving Repr

/-- *expect* is ambiguous between future irrealis and propositional
    (@cite{wurmbrand-2014} §3, §4.3).

    - Future: "The bridge is expected to collapse right now"
      ≈ scheduled to collapse (near future)
    - Propositional: "I expected Leo to be sleeping then"
      ≈ believed Leo was sleeping (simultaneous)

    Under the propositional reading, bare episodic interpretations
    are impossible (only imperfective/progressive is possible), just
    like *believe*. Under the future reading, episodic interpretations
    are possible, just like *decide*. -/
def expect : AmbiguousVerb := ⟨"expect", [.futureIrrealis, .propositional]⟩

/-- *seem* is primarily tenseless simultaneous (like *try*, *begin*),
    but can also be construed propositionally when an experiencer is
    present (@cite{wurmbrand-2014} §4.4).

    - Without experiencer: "The bridge seemed to tremble" →
      tenseless, dependent on matrix tense
    - With experiencer: "John seems to be sleeping" →
      can use the experiencer's NOW as reference time,
      patterning with propositional attitude infinitives -/
def seem : AmbiguousVerb := ⟨"seem", [.restructuring, .propositional]⟩

/-- *expect* admits both future and propositional readings. -/
theorem expect_is_ambiguous :
    expect.readings.length > 1 := by native_decide

/-- *seem* admits both restructuring and propositional readings. -/
theorem seem_is_ambiguous :
    seem.readings.length > 1 := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 8: Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Future-irrealis infinitives are future-oriented: the future
    orientation comes from woll, not from tense. -/
theorem futureIrrealis_is_future_oriented :
    classOrientation .futureIrrealis = .futureOriented := rfl

/-- Propositional infinitives impose NOW-anchoring: the complement's
    reference time is simultaneous with the attitude holder's time. -/
theorem propositional_now_anchored :
    classOrientation .propositional = .simultaneous := rfl

/-- Restructuring infinitives share the matrix temporal domain: there is
    no independent temporal reference in the complement. -/
theorem restructuring_dependent :
    classOrientation .restructuring = .dependent := rfl

/-- All three classes are represented. -/
theorem wurmbrand_three_classes_distinct :
    want.tenseClass ≠ believe.tenseClass ∧
    believe.tenseClass ≠ try_.tenseClass ∧
    want.tenseClass ≠ try_.tenseClass := by
  exact ⟨nofun, nofun, nofun⟩


-- ════════════════════════════════════════════════════════════════
-- § 9: Bridge Theorems
-- ════════════════════════════════════════════════════════════════

/-- Propositional NOW-anchoring connects to the tense pronoun
    architecture: propositional infinitives require that the
    complement's reference time be anchored to a shifted evaluation
    time (the attitude holder's NOW), exactly as `AttitudeTemporalSemantics`
    specifies via `shiftEvalTime`.

    `standardShift` computes embedded eval time as matrix event time.
    Propositional infinitives use this as their reference time, yielding
    the simultaneous reading. -/
theorem propositional_uses_attitude_eval_time :
    classOrientation .propositional = .simultaneous ∧
    (standardShift (Time := ℕ)).shiftEvalTime
      { speechTime := 0, perspectiveTime := 0, referenceTime := 0, eventTime := 5 } = 5 :=
  ⟨rfl, rfl⟩

/-- Restructuring infinitives lack independent tense: they share the
    matrix temporal domain. This manifests as both `dependent` orientation
    AND the smallest complement size (`vP_AspP`) AND absence of woll. -/
theorem restructuring_minimal_structure :
    classOrientation .restructuring = .dependent ∧
    classToSize .restructuring = .vP_AspP ∧
    classHasWoll .restructuring = false :=
  ⟨rfl, rfl, rfl⟩

/-- Future-oriented complements have woll AND project a wollP: the
    future modal is structurally present. This is what distinguishes
    the temporal composition of future infinitives from the other two
    classes: future orientation comes from a syntactic element (*woll*),
    not from the lexical semantics of the matrix predicate alone. -/
theorem futureIrrealis_structural_future :
    classHasWoll .futureIrrealis = true ∧
    classToSize .futureIrrealis = .wollP ∧
    classOrientation .futureIrrealis = .futureOriented :=
  ⟨rfl, rfl, rfl⟩

/-- The three classes form a decreasing complement size hierarchy:
    wollP > TP > vP/AspP. This is @cite{wurmbrand-2001}'s insight
    that restructuring is complement truncation from the top. -/
theorem complement_size_hierarchy :
    (classToSize .futureIrrealis).isLargerThan (classToSize .propositional) = true ∧
    (classToSize .propositional).isLargerThan (classToSize .restructuring) = true :=
  ⟨rfl, rfl⟩

/-- Woll presence correlates exactly with future orientation:
    a class has woll iff its orientation is future-oriented. -/
theorem woll_iff_future :
    ∀ c : InfinitivalTenseClass,
      classHasWoll c = true ↔ classOrientation c = .futureOriented := by
  intro c; cases c <;> simp [classHasWoll, classOrientation]

/-- Episodic availability correlates with complement size: larger
    complements (with their own temporal elements) allow episodic
    interpretations independent of the matrix, while smaller complements
    (lacking independent temporal structure) are matrix-dependent. -/
theorem episodic_correlates_with_size :
    classEpisodicPrediction .futureIrrealis = .possible ∧
    classToSize .futureIrrealis = .wollP ∧
    classEpisodicPrediction .propositional = .impossible ∧
    classToSize .propositional = .tP ∧
    classEpisodicPrediction .restructuring = .matrixDependent ∧
    classToSize .restructuring = .vP_AspP :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


end Minimalism.Tense.InfinitivalTense
