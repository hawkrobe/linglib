import Linglib.Data.WALS.Features.F117A
import Linglib.Data.WALS.Features.F118A
import Linglib.Data.WALS.Features.F119A
import Linglib.Data.WALS.Features.F120A

/-!
# Typology.Copulas
[stassen-2013] [hengeveld-1992] [pustet-2003]
[haspelmath-2001]

Per-language typological substrate for copula and predication strategies,
covering WALS chapters 117--120 (all four authored by Leon Stassen):

- **Ch 117** (Stassen): Predicative possession ("I have a book"). N = 240.
- **Ch 118** (Stassen): Predicative adjectives ("The book is red"). N = 386.
- **Ch 119** (Stassen): Nominal and locational predication
  ("She is a doctor" vs "The cat is on the mat"). N = 386.
- **Ch 120** (Stassen): Zero copula for predicate nominals. N = 386.

Mirrors the `Linglib/Typology/{Possession,Negation,Comparison,Coordination,
Modality,Gender,Alignment,ArgumentStructure}` substrate-extension pattern.
Fragment-importable.

## What lives here

- `PredAdjStrategy` (Ch 118: verbal/mixed/nonVerbal).
- `PredNounStrategy` (binary verbal/nonVerbal — finer than any single WALS
  chapter; maps to neither F117A nor F118A).
- `NomLocStrategy` (Ch 119: identical/different).
- `ZeroCopulaStatus` (Ch 120 + finer: impossible/restricted/widespread,
  whereas WALS F120A only distinguishes impossible vs. possible).
- `CopulaType` (supplementary: verbal/pronominal/particle/zero, after
  [pustet-2003] and [hengeveld-1992]).
- `CopulaProfile` per-language struct.
- WALS converters `fromWALS{118A, 119A, 120A}` + the `wals120A_allowsZero`
  weakening predicate (since F120A collapses restricted/widespread).
- WALS aggregate sample-size + corpus-only theorems.

## Theory-laden caveats

- **`predNoun` is not anchored on a single WALS chapter.** It cuts across
  Ch 119 + Ch 120: a language with verbal nominal predication needs a verbal
  copula form (visible across both chapters), but there is no WALS chapter
  asking the binary question directly.
- **`ZeroCopulaStatus` is finer than WALS F120A.** F120A has only
  `impossible/possible`; the substrate distinguishes `restricted` (e.g.
  Russian present-tense only) from `widespread` (e.g. Tagalog default).
  `fromWALS120A` returns `Option ZeroCopulaStatus` for the F120A.possible
  case (truly ambiguous). `wals120A_allowsZero` is the decidable weakening.

## Out of scope

The 20-language `CopulaProfile` sample, cross-chapter correlations
(Stassen's implication, areal patterns, copula-type distributions), and
Fragment-bridge theorems live in `Studies/Stassen2013.lean`.
Partee's compositional `BE` type-shift bridge to copula typology is in
`Studies/Partee1987.lean`.
-/

set_option autoImplicit false

namespace Typology.Copulas

private abbrev ch117 := Data.WALS.F117A.allData
private abbrev ch118 := Data.WALS.F118A.allData
private abbrev ch119 := Data.WALS.F119A.allData
private abbrev ch120 := Data.WALS.F120A.allData

-- ============================================================================
-- §1. WALS Ch 118: Predicative Adjective Strategy
-- ============================================================================

/-- WALS Ch 118: How a language expresses adjectival predication
    ("The book is red").

    The three-way distinction reflects the categorial status of adjectives
    in the language. In "verbal" languages, adjectives inflect like verbs
    and need no copula. In "non-verbal" languages, adjectives are a
    distinct category requiring a copula. "Mixed" languages have adjectives
    that split between verbal and non-verbal behavior. -/
inductive PredAdjStrategy where
  /-- Adjectives behave like verbs: they take verbal morphology (tense,
      aspect, negation) and occur as predicates without a copula.
      Example: Mandarin `shu hong` 'book red' = 'The book is red',
      where `hong` can take aspect markers directly. -/
  | verbal
  /-- Some adjectives are verbal (typically core/frequent ones), others
      require a copula (typically peripheral/borrowed ones).
      Example: Japanese has verbal adjectives (i-adjectives: `takai`
      'is expensive') and non-verbal adjectives (na-adjectives: `shizuka-da`
      'quiet-COP'). -/
  | mixed
  /-- Adjectives are categorially distinct from verbs and require a
      copula or other linking element for predication.
      Example: English `The book is red` requires the copula `is`. -/
  | nonVerbal
  deriving DecidableEq, Repr

instance : Inhabited PredAdjStrategy := ⟨.nonVerbal⟩

-- ============================================================================
-- §2. Predicative Noun Strategy (cross-cuts Ch 118--120)
-- ============================================================================

/-- How a language expresses nominal predication ("She is a doctor").

    The binary distinction captures whether the language uses a verbal
    copula (a word that inflects like a verb and carries tense/agreement)
    or a non-verbal strategy (juxtaposition, pronominal copula, or
    invariant particle). Not anchored on a single WALS chapter; visible
    across F119A + F120A. -/
inductive PredNounStrategy where
  /-- Nominal predication uses a verbal copula that inflects for tense,
      agreement, etc.
      Example: English `She is a doctor`, where `is` is a fully inflecting
      verb (am/is/are/was/were). -/
  | verbal
  /-- Nominal predication uses juxtaposition or a non-verbal element
      (particle, pronoun, etc.), not a copula verb.
      Example: Russian present tense `Ona vrach` 'She doctor' = 'She is
      a doctor' (no copula in present tense). -/
  | nonVerbal
  deriving DecidableEq, Repr

-- ============================================================================
-- §3. WALS Ch 119: Nominal vs Locational Predication
-- ============================================================================

/-- WALS Ch 119: Whether a language uses the same or different strategy
    for nominal predication ("She is a doctor") and locational predication
    ("The cat is on the mat").

    Many languages use different verbs: e.g., Spanish `ser` (nominal) vs
    `estar` (locational), or have a copula for one but not the other. The
    "different" value is the majority pattern cross-linguistically. -/
inductive NomLocStrategy where
  /-- The same copula or strategy is used for both nominal and locational
      predication.
      Example: English `She is a doctor` / `The cat is on the mat` --
      both use `be`. -/
  | identical
  /-- Different copulas or strategies are used for nominal vs locational
      predication.
      Example: Spanish `ser` (nominal: `Es doctora`) vs `estar`
      (locational: `Esta en la casa`). -/
  | different
  deriving DecidableEq, Repr

-- ============================================================================
-- §4. WALS Ch 120: Zero Copula (extended with restricted/widespread)
-- ============================================================================

/-- Zero copula status, extending WALS F120A's binary impossible/possible
    with the standard restricted/widespread distinction.

    Zero copula is typically conditioned by tense (present only) or
    person (3rd person only). "Widespread" means zero copula is the
    default, unrestricted strategy. -/
inductive ZeroCopulaStatus where
  /-- Zero copula is impossible: the copula is always required in nominal
      predication, regardless of tense, person, or other factors.
      Example: English `*She doctor` is ungrammatical. -/
  | impossible
  /-- Zero copula is possible in restricted contexts: typically present
      tense, or 3rd person, or in certain clause types. The copula
      appears in other environments.
      Example: Russian allows zero copula in present tense
      (`Ona vrach` 'She doctor') but requires it in past tense
      (`Ona byla vrach` 'She was doctor'). -/
  | restricted
  /-- Zero copula is the normal, widespread, or default strategy.
      The copula is absent in most environments.
      Example: Tagalog `Doktor siya` 'Doctor she' = 'She is a doctor'. -/
  | widespread
  deriving DecidableEq, Repr

-- ============================================================================
-- §5. CopulaType (supplementary: Pustet 2003, Hengeveld 1992)
-- ============================================================================

/-- Morphosyntactic type of copula, when present.

    Supplements the WALS classification with a finer-grained typology of
    copular elements, following [pustet-2003] and [hengeveld-1992]. -/
inductive CopulaType where
  /-- Fully inflecting verbal copula: takes tense, agreement, negation
      like other verbs. Example: English `be` (am/is/are/was/were). -/
  | verbalCopula
  /-- Pronominal copula: a pronoun-like element that agrees with the
      subject. Example: Hebrew `hu/hi/hem/hen` (he/she/they.m/they.f)
      used as a copula in present tense. -/
  | pronominalCopula
  /-- Invariant particle: a non-inflecting element linking subject and
      predicate. Example: Swahili `ni` (affirmative copula, invariant). -/
  | particle
  /-- No copula: predication by juxtaposition. -/
  | zero
  deriving DecidableEq, Repr

-- ============================================================================
-- §6. CopulaProfile (Fragment-side joint)
-- ============================================================================

/-- A language's copula and predication profile across WALS Chs 118--120
    + supplementary copula-type information. -/
structure CopulaProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Language family. -/
  family : String := ""
  /-- Ch 118: How adjectival predication is expressed. -/
  predAdj : PredAdjStrategy
  /-- How nominal predication is expressed (cross-cuts Ch 119/120). -/
  predNoun : PredNounStrategy
  /-- Ch 119: Whether nominal and locational predication use the
      same or different strategy. -/
  nomLoc : NomLocStrategy
  /-- Ch 120: Whether zero copula is possible in nominal predication
      (extended with restricted/widespread). -/
  zeroCopula : ZeroCopulaStatus
  /-- Primary copula type in the language (supplementary). -/
  copulaType : CopulaType := .verbalCopula
  /-- Illustrative copula form(s). -/
  copulaForms : List String := []
  /-- Notes on the predication system. -/
  notes : String := ""
  deriving Repr

/-- Does a language have verbal adjectives? -/
def CopulaProfile.hasVerbalAdj (p : CopulaProfile) : Bool :=
  p.predAdj == .verbal

/-- Does a language have a verbal copula for nominal predication? -/
def CopulaProfile.hasVerbalNounCopula (p : CopulaProfile) : Bool :=
  p.predNoun == .verbal

/-- Does a language allow zero copula (restricted or widespread)? -/
def CopulaProfile.allowsZeroCopula (p : CopulaProfile) : Bool :=
  p.zeroCopula == .restricted || p.zeroCopula == .widespread

/-- Does a language split nominal and locational predication? -/
def CopulaProfile.hasNomLocSplit (p : CopulaProfile) : Bool :=
  p.nomLoc == .different

/-- Does a language require a copula in all contexts? -/
def CopulaProfile.alwaysRequiresCopula (p : CopulaProfile) : Bool :=
  p.zeroCopula == .impossible

-- ============================================================================
-- §7. WALS converters
-- ============================================================================

/-- Map WALS F118A (predicative adjectives) to `PredAdjStrategy`. -/
def fromWALS118A : Data.WALS.F118A.PredicativeAdjectiveType → PredAdjStrategy
  | .verbalEncoding    => .verbal
  | .nonverbalEncoding => .nonVerbal
  | .mixed             => .mixed

/-- Map WALS F119A (nominal and locational predication) to `NomLocStrategy`. -/
def fromWALS119A : Data.WALS.F119A.NominalLocationalPredication → NomLocStrategy
  | .different => .different
  | .identical => .identical

/-- Map WALS F120A (zero copula) to `ZeroCopulaStatus`.

    F120A has only two values (impossible/possible), while
    `ZeroCopulaStatus` distinguishes restricted from widespread within
    "possible." The mapping is therefore lossy: `.impossible` maps exactly,
    but `.possible` is ambiguous between `.restricted` and `.widespread`.
    Returns `Option` for the ambiguous case. -/
def fromWALS120A : Data.WALS.F120A.ZeroCopulaType → Option ZeroCopulaStatus
  | .impossible => some .impossible
  | .possible   => none

/-- Decidable weakening of `fromWALS120A`: does WALS F120A say zero copula
    is at least possible? Suitable for cross-checking against
    `CopulaProfile.allowsZeroCopula`. -/
def wals120A_allowsZero : Data.WALS.F120A.ZeroCopulaType → Bool
  | .impossible => false
  | .possible   => true


/-- Chs 118, 119, 120 use the same 386-language sample. Ch 117 uses a
    smaller 240-language sample. -/
theorem ch118_119_120_same_sample :
    ch118.length = ch119.length ∧ ch119.length = ch120.length := by
  native_decide

-- ============================================================================
-- §9. Theory-neutral WALS distribution facts
-- ============================================================================

/-- Ch 118 cell counts (from [stassen-2013]'s map). -/
theorem ch118_verbal_count :
    (ch118.filter (·.value == .verbalEncoding)).length = 151 := by native_decide
theorem ch118_nonverbal_count :
    (ch118.filter (·.value == .nonverbalEncoding)).length = 132 := by native_decide
theorem ch118_mixed_count :
    (ch118.filter (·.value == .mixed)).length = 103 := by native_decide

/-- Ch 119 cell counts. -/
theorem ch119_different_count :
    (ch119.filter (·.value == .different)).length = 269 := by native_decide
theorem ch119_identical_count :
    (ch119.filter (·.value == .identical)).length = 117 := by native_decide

/-- Ch 120 cell counts. -/
theorem ch120_impossible_count :
    (ch120.filter (·.value == .impossible)).length = 211 := by native_decide
theorem ch120_possible_count :
    (ch120.filter (·.value == .possible)).length = 175 := by native_decide

/-- Ch 117 cell counts. -/
theorem ch117_locational_count :
    (ch117.filter (·.value == .locational)).length = 48 := by native_decide
theorem ch117_genitive_count :
    (ch117.filter (·.value == .genitive)).length = 22 := by native_decide
theorem ch117_topic_count :
    (ch117.filter (·.value == .topic)).length = 48 := by native_decide
theorem ch117_conjunctional_count :
    (ch117.filter (·.value == .conjunctional)).length = 59 := by native_decide
theorem ch117_have_count :
    (ch117.filter (·.value == .have)).length = 63 := by native_decide

/-- Ch 118: verbal encoding is the most common strategy for predicative
    adjectives, exceeding both mixed and nonverbal encoding. -/
theorem verbal_adj_most_common :
    (ch118.filter (·.value == .verbalEncoding)).length >
      (ch118.filter (·.value == .nonverbalEncoding)).length ∧
    (ch118.filter (·.value == .verbalEncoding)).length >
      (ch118.filter (·.value == .mixed)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 118: verbal adjectives account for roughly 39% of the sample. -/
theorem verbal_adj_plurality :
    (ch118.filter (·.value == .verbalEncoding)).length * 3 > ch118.length := by
  native_decide

/-- Ch 118: no single predicative adjective strategy is a strict majority. -/
theorem no_adj_strategy_majority :
    (ch118.filter (·.value == .verbalEncoding)).length * 2 < ch118.length := by
  native_decide

/-- Ch 119: using different strategies for nominal and locational
    predication is more common than using the same strategy.
    Languages typically distinguish "is a doctor" from "is in the room"
    with different grammatical means. -/
theorem nomloc_split_majority :
    (ch119.filter (·.value == .different)).length >
    (ch119.filter (·.value == .identical)).length := by native_decide

/-- Ch 119: the split pattern is a clear supermajority (more than half). -/
theorem nomloc_split_supermajority :
    (ch119.filter (·.value == .different)).length > ch119.length / 2 := by
  native_decide

/-- Ch 120: "Impossible" (copula always required) is the majority value. -/
theorem zero_impossible_majority :
    (ch120.filter (·.value == .impossible)).length >
    (ch120.filter (·.value == .possible)).length := by
  native_decide

/-- Ch 120: "Impossible" accounts for more than half the sample. -/
theorem zero_impossible_over_half :
    (ch120.filter (·.value == .impossible)).length > ch120.length / 2 := by
  native_decide

end Typology.Copulas
