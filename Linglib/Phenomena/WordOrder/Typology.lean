import Linglib.Core.Lexical.Word
import Linglib.Core.Typology.WordOrder
import Linglib.Core.Typology.Adposition
import Linglib.Core.Typology.LanguageProfile
import Linglib.Core.Typology.Universal
import Linglib.Fragments.English.Typology
import Linglib.Fragments.Japanese.Typology
import Linglib.Fragments.Mandarin.Typology
import Linglib.Fragments.Korean.Typology
import Linglib.Fragments.Arabic.Typology
import Linglib.Core.WALS.Features.F81A
import Linglib.Core.WALS.Features.F82A
import Linglib.Core.WALS.Features.F83A
import Linglib.Core.WALS.Features.F87A
import Linglib.Core.WALS.Features.F88A
import Linglib.Core.WALS.Features.F90A
import Linglib.Core.WALS.Features.F94A
import Linglib.Core.WALS.Features.F95A
import Linglib.Core.WALS.Features.F96A
import Linglib.Core.WALS.Features.F97A
import Linglib.Core.WALS.Features.F81B
import Linglib.Core.WALS.Features.F90B
import Linglib.Core.WALS.Features.F90C
import Linglib.Core.WALS.Features.F60A
import Linglib.Core.WALS.Features.F61A

/-!
# Word-Order Typology (@cite{dryer-haspelmath-2013} / WALS)
@cite{dryer-1992} @cite{dryer-haspelmath-2013} @cite{gibson-2025} @cite{greenberg-1963}

WALS data from @cite{gibson-2025}: cross-linguistic counts
of harmonic vs disharmonic word-order pairings. @cite{dryer-1992} documents
that languages overwhelmingly prefer consistent head direction across
construction types (the **head-direction generalization**, @cite{greenberg-1963}).

## Data

Three cross-tabulations from WALS:
- **Table 1**: VO × Adposition order (981 languages)
- **Table 2**: VO × Subordinator order (456 languages)
- **Table 3**: VO × Relative clause order (665 languages)

Each table is a 2×2 contingency table: VO/OV × head-initial/head-final for
the second construction. Harmonic cells (both HI or both HF) dominate.

## Single-Word Exceptions (Table 4)

Some constructions show *disharmonic* tendencies cross-linguistically:
adjective-noun, demonstrative-noun, intensifier-adjective, negator-verb.
@cite{gibson-2025} argues these are cases where the dependent is a single word
(no recursive subtree), so head direction is irrelevant to DLM.

## Per-language profiles

Per-language records live in `Fragments/{Lang}/Typology.lean` (when they carry
overrides) or are inlined as `Core.Typology.LanguageProfile.ofWALS` directly
in `fragmentSample` (when pure WALS suffices). The legacy `BasicOrderProfile`
struct and its 21 hand-curated language defs have been retired in favour of
that source-of-truth chain.

## Greenbergian universals

`fragmentSample : Finset LanguageProfile` is the curated 15-language sample
used to state cross-linguistic implicational universals (@cite{greenberg-1963}
U3 and U4 are stated and proved here as `greenberg_universal_3`/`_4`). Cross-
chapter consistency theorems (`sov_implies_sv_and_ov`, ...) verify that WALS
Ch 81/82/83 agree per language for sampled languages.

-/

namespace Phenomena.WordOrder.Typology

-- ============================================================================
-- Types
-- ============================================================================

-- HeadDirection is defined in Core.Basic (imported transitively)

/-- A single cell in a 2×2 alignment table.
    `dir1` is the direction for the first construction (verb-object order),
    `dir2` is the direction for the second construction. -/
structure AlignmentCell where
  dir1 : HeadDirection
  dir2 : HeadDirection
  count : Nat
  deriving Repr, DecidableEq

/-- Whether an alignment cell represents a harmonic (consistent-direction) pair. -/
def AlignmentCell.isHarmonic (c : AlignmentCell) : Bool :=
  c.dir1 == c.dir2

/-- A 2×2 cross-tabulation of two construction types. -/
structure CrossTab where
  name : String
  construction1 : String  -- e.g. "Verb-Object"
  construction2 : String  -- e.g. "Adposition"
  hihi : AlignmentCell     -- both head-initial
  hihf : AlignmentCell     -- construction 1 HI, construction 2 HF
  hfhi : AlignmentCell     -- construction 1 HF, construction 2 HI
  hfhf : AlignmentCell     -- both head-final
  deriving Repr

/-- Total count of harmonic (diagonal) cells. -/
def CrossTab.harmonicCount (t : CrossTab) : Nat :=
  t.hihi.count + t.hfhf.count

/-- Total count of disharmonic (off-diagonal) cells. -/
def CrossTab.disharmonicCount (t : CrossTab) : Nat :=
  t.hihf.count + t.hfhi.count

/-- Total number of languages in the table. -/
def CrossTab.totalCount (t : CrossTab) : Nat :=
  t.harmonicCount + t.disharmonicCount

/-- Whether harmonic pairings are the majority. -/
def CrossTab.harmonicDominant (t : CrossTab) : Bool :=
  t.harmonicCount > t.disharmonicCount

-- ============================================================================
-- Data: @cite{gibson-2025} Tables 1–3
-- ============================================================================

/-- Table 1: Verb-Object order × Adposition order (@cite{dryer-haspelmath-2013}, WALS).
    @cite{gibson-2025} Table 1. 981 languages. -/
def voAdposition : CrossTab :=
  { name := "VO × Adposition"
    construction1 := "Verb-Object"
    construction2 := "Adposition"
    hihi := ⟨.headInitial, .headInitial, 454⟩
    hihf := ⟨.headInitial, .headFinal, 41⟩
    hfhi := ⟨.headFinal, .headInitial, 14⟩
    hfhf := ⟨.headFinal, .headFinal, 472⟩ }

/-- Table 2: Verb-Object order × Subordinator order (@cite{dryer-haspelmath-2013}, WALS).
    @cite{gibson-2025} Table 2. 456 languages. -/
def voSubordinator : CrossTab :=
  { name := "VO × Subordinator"
    construction1 := "Verb-Object"
    construction2 := "Subordinator"
    hihi := ⟨.headInitial, .headInitial, 302⟩
    hihf := ⟨.headInitial, .headFinal, 2⟩
    hfhi := ⟨.headFinal, .headInitial, 61⟩
    hfhf := ⟨.headFinal, .headFinal, 91⟩ }

/-- Table 3: Verb-Object order × Relative clause order (@cite{dryer-haspelmath-2013}, WALS).
    @cite{gibson-2025} Table 3. 665 languages. -/
def voRelativeClause : CrossTab :=
  { name := "VO × Relative clause"
    construction1 := "Verb-Object"
    construction2 := "Relative clause"
    hihi := ⟨.headInitial, .headInitial, 415⟩
    hihf := ⟨.headInitial, .headFinal, 5⟩
    hfhi := ⟨.headFinal, .headInitial, 113⟩
    hfhf := ⟨.headFinal, .headFinal, 132⟩ }

/-- All three cross-tabulations from @cite{gibson-2025}. -/
def allTables : List CrossTab :=
  [voAdposition, voSubordinator, voRelativeClause]

-- ============================================================================
-- Harmonic vs Disharmonic: Per-Table Theorems
-- ============================================================================

/-- Table 1: harmonic (926) > disharmonic (55). -/
theorem voAdposition_harmonic_dominant :
    voAdposition.harmonicDominant = true := by decide

/-- Table 2: harmonic (393) > disharmonic (63). -/
theorem voSubordinator_harmonic_dominant :
    voSubordinator.harmonicDominant = true := by decide

/-- Table 3: harmonic (547) > disharmonic (118). -/
theorem voRelativeClause_harmonic_dominant :
    voRelativeClause.harmonicDominant = true := by decide

-- ============================================================================
-- The Head-Direction Generalization (@cite{greenberg-1963} / @cite{dryer-1992})
-- ============================================================================

/-- The head-direction generalization: across all three construction pairs,
    harmonic word-order pairings dominate.

    This is the core empirical observation that @cite{gibson-2025}
    argues DLM explains: consistent head direction keeps recursive spine
    dependencies local. -/
theorem head_direction_generalization :
    allTables.all CrossTab.harmonicDominant = true := by decide

-- ============================================================================
-- Harmonic cells are themselves diagonal
-- ============================================================================

/-- Harmonic cells have matching directions. -/
theorem hihi_is_harmonic : voAdposition.hihi.isHarmonic = true := by decide
theorem hfhf_is_harmonic : voAdposition.hfhf.isHarmonic = true := by decide

/-- Disharmonic cells have mismatched directions. -/
theorem hihf_is_disharmonic : voAdposition.hihf.isHarmonic = false := by decide
theorem hfhi_is_disharmonic : voAdposition.hfhi.isHarmonic = false := by decide

-- ============================================================================
-- Single-Word Exceptions (Gibson Table 4)
-- ============================================================================

/-- Construction types where disharmonic order is common (Gibson Table 4).

    These are cases where the dependent is typically a single word (no recursive
    subtree), so head direction doesn't affect DLM. Gibson's argument: DLM
    only cares about direction when subtrees intervene between head and dependent.

    Data here is qualitative — WALS counts not provided in Gibson for these.
    Marked as data TBD for future WALS lookup. -/
inductive SingleWordException where
  | adjN         -- adjective-noun: many VO languages have Adj-N (head-final order)
  | demN         -- demonstrative-noun: many OV languages have Dem-N (head-initial order)
  | intensAdj    -- intensifier-adjective: "very tall" is head-initial in many OV languages
  | negVerb      -- negator-verb: "not run" is head-initial in many OV languages
  deriving Repr, DecidableEq

/-- All single-word exceptions from Gibson Table 4. -/
def singleWordExceptions : List SingleWordException :=
  [.adjN, .demN, .intensAdj, .negVerb]

/-- These exceptions all involve dependents that are typically single words
    (leaves in the dependency tree), not recursive phrases. -/
def isSingleWordDependent : SingleWordException → Prop
  | .adjN => True        -- adjectives are typically leaves
  | .demN => True        -- demonstratives are single words
  | .intensAdj => True   -- intensifiers like "very" are single words
  | .negVerb => True     -- negation markers are single words

instance : DecidablePred isSingleWordDependent := fun x => by
  cases x <;> unfold isSingleWordDependent <;> infer_instance

theorem all_exceptions_single_word :
    ∀ e ∈ singleWordExceptions, isSingleWordDependent e := by decide

-- ============================================================================
-- WALS Distribution Data — derived from generated modules
-- ============================================================================
-- Full per-language data lives in Core.WALS.Features.F{81A,82A,83A,...}.
-- Aggregate counts are derived from the generated data by filtering.

-- ============================================================================
-- Word-order types (re-exported from Core.Typology.WordOrder)
-- ============================================================================
-- The order enums (`BasicOrder`, `SVOrder`, `OVOrder`) and the WALS
-- conversion helpers live in `Core/Typology/WordOrder.lean` so that both
-- this file and per-language Fragments can import them without violating
-- the layered dependency hierarchy. They are re-exported here for the
-- convenience of consumers that already `open Phenomena.WordOrder.Typology`.

export Core.Typology.WordOrder
  ( BasicOrder SVOrder OVOrder WordOrderProfile
    fromWALS81A fromWALS82A fromWALS83A
    basicOrderOfWALS svOrderOfWALS ovOrderOfWALS )

-- ============================================================================
-- Typological Generalizations
-- ============================================================================

-- WALS chapter abbreviations for filter-counting generalizations.
private abbrev ch81 := Core.WALS.F81A.allData
private abbrev ch82 := Core.WALS.F82A.allData
private abbrev ch83 := Core.WALS.F83A.allData
private abbrev ch87 := Core.WALS.F87A.allData
private abbrev ch88 := Core.WALS.F88A.allData
private abbrev ch90 := Core.WALS.F90A.allData
private abbrev ch94 := Core.WALS.F94A.allData
private abbrev ch95 := Core.WALS.F95A.allData
private abbrev ch96 := Core.WALS.F96A.allData
private abbrev ch97 := Core.WALS.F97A.allData
private abbrev ch81B := Core.WALS.F81B.allData
private abbrev ch90B := Core.WALS.F90B.allData
private abbrev ch90C := Core.WALS.F90C.allData
private abbrev ch60 := Core.WALS.F60A.allData
private abbrev ch61 := Core.WALS.F61A.allData

set_option maxRecDepth 8192 in
/-- Generalization 1: SOV is the most common basic order. -/
theorem sov_most_common :
    (ch81.filter (·.value == .sov)).length >
    (ch81.filter (·.value == .svo)).length := by decide

set_option maxRecDepth 8192 in
/-- Generalization 2: SOV + SVO together exceed 75% of all sampled languages. -/
theorem sov_svo_majority_overall :
    let sov := (ch81.filter (·.value == .sov)).length
    let svo := (ch81.filter (·.value == .svo)).length
    (sov + svo) * 4 > ch81.length * 3 := by decide

set_option maxRecDepth 8192 in
/-- Generalization 3: In Ch 83, OV slightly outnumbers VO. -/
theorem ov_dominant_ch83 :
    (ch83.filter (·.value == .ov)).length >
    (ch83.filter (·.value == .vo)).length := by decide

set_option maxRecDepth 8192 in
/-- Generalization 4: Subject-first orders (SOV + SVO) far outnumber
    verb-first orders (VSO + VOS). -/
theorem subject_first_dominant :
    let sf := (ch81.filter (·.value == .sov)).length +
              (ch81.filter (·.value == .svo)).length
    let vf := (ch81.filter (·.value == .vso)).length +
              (ch81.filter (·.value == .vos)).length
    sf > vf * 8 := by decide

set_option maxRecDepth 8192 in
/-- Generalization 5: Object-initial orders (OVS + OSV) are extremely
    rare — less than 2% of the sample. -/
theorem object_initial_rare :
    let oi := (ch81.filter (·.value == .ovs)).length +
              (ch81.filter (·.value == .osv)).length
    oi * 100 < ch81.length * 2 := by decide

set_option maxRecDepth 8192 in
/-- Generalization 6 (Greenberg's Universal 1): In declarative sentences with
    nominal subject and object, the subject almost always precedes the object.
    SOV + SVO + VSO (subject before object) vastly outnumber
    VOS + OVS + OSV (object before subject). -/
theorem greenberg_universal_1 :
    let subj_before_obj := (ch81.filter (·.value == .sov)).length +
                           (ch81.filter (·.value == .svo)).length +
                           (ch81.filter (·.value == .vso)).length
    let obj_before_subj := (ch81.filter (·.value == .vos)).length +
                           (ch81.filter (·.value == .ovs)).length +
                           (ch81.filter (·.value == .osv)).length
    subj_before_obj > obj_before_subj * 28 := by decide

set_option maxRecDepth 8192 in
/-- Generalization 7: SV overwhelmingly dominates VS in Ch 82.
    SV languages outnumber VS languages by more than 5 to 1. -/
theorem sv_dominant :
    (ch82.filter (·.value == .sv)).length >
    (ch82.filter (·.value == .vs)).length * 5 := by decide

-- ============================================================================
-- Per-Chapter Generalizations
-- ============================================================================

set_option maxRecDepth 8192 in
/-- Ch 87: N-Adj order dominates cross-linguistically (one of Gibson's
    single-word exceptions: adjectives are typically leaves). -/
theorem nounAdj_dominant_ch87 :
    (ch87.filter (·.value == .nounAdjective)).length >
    (ch87.filter (·.value == .adjectiveNoun)).length * 2 := by decide

set_option maxRecDepth 8192 in
/-- Ch 88: Dem-N vs N-Dem is roughly balanced (another single-word exception:
    demonstratives are single words, so head direction is less predictive). -/
theorem demN_roughly_balanced_ch88 :
    let demN := (ch88.filter (·.value == .demonstrativeNoun)).length
    let nDem := (ch88.filter (·.value == .nounDemonstrative)).length
    demN * 10 > nDem * 9 := by decide

set_option maxRecDepth 8192 in
/-- Ch 90: N-RelCl strongly dominates (relative clauses are recursive phrases,
    not single words — head direction matters). -/
theorem nounRelCl_dominant_ch90 :
    (ch90.filter (·.value == .nounRelativeClause)).length >
    (ch90.filter (·.value == .relativeClauseNoun)).length * 4 := by decide

set_option maxRecDepth 8192 in
/-- Ch 94: Initial subordinator words are the most common strategy for
    adverbial subordination. -/
theorem initial_subordinator_dominant_ch94 :
    (ch94.filter (·.value == .initialSubordinatorWord)).length >
    (ch94.filter (·.value == .finalSubordinatorWord)).length * 4 := by decide

set_option maxRecDepth 8192 in
/-- Ch 95: Harmonic pairs (OV+Postp, VO+Prep) vastly outnumber disharmonic
    (OV+Prep, VO+Postp). -/
theorem ch95_harmonic_dominant :
    let harmonic := (ch95.filter (·.value == .ovAndPostpositions)).length +
                    (ch95.filter (·.value == .voAndPrepositions)).length
    let disharmonic := (ch95.filter (·.value == .ovAndPrepositions)).length +
                       (ch95.filter (·.value == .voAndPostpositions)).length
    harmonic > disharmonic * 16 := by decide

set_option maxRecDepth 8192 in
/-- Ch 96: VO+NRel strongly dominates VO+RelN (relative clauses are recursive,
    so head direction matters). OV languages are more mixed due to the N-RelCl
    strategy. -/
theorem ch96_voNRel_dominant :
    (ch96.filter (·.value == .voAndNrel)).length >
    (ch96.filter (·.value == .voAndReln)).length * 80 := by decide

set_option maxRecDepth 8192 in
/-- Ch 97: OV languages split between AdjN and NAdj (weak correlation,
    single-word exception). This contrasts with Ch 95 where OV+Prep is
    nearly absent. -/
theorem ch97_ov_split :
    let ovAdjN := (ch97.filter (·.value == .ovAndAdjn)).length
    let ovNAdj := (ch97.filter (·.value == .ovAndNadj)).length
    ovNAdj > ovAdjN := by decide

set_option maxRecDepth 8192 in
/-- Ch 81B: SOV-or-SVO is the most common dual-order pattern, consistent
    with the general dominance of subject-first orders. -/
theorem ch81B_sovOrSvo_most_common :
    (ch81B.filter (·.value == .sovOrSvo)).length >
    (ch81B.filter (·.value == .vsoOrVos)).length := by decide

set_option maxRecDepth 4096 in
/-- Ch 90B: Dominant-only prenominal (RelN) is the majority among languages
    with this strategy. -/
theorem ch90B_dominant_relN_majority :
    (ch90B.filter (·.value == .relativeClauseNounDominant)).length >
    ch90B.length / 2 := by decide

set_option maxRecDepth 4096 in
/-- Ch 90C: Dominant-only postnominal (NRel) is overwhelmingly the majority
    among languages with this strategy. -/
theorem ch90C_dominant_nRel_majority :
    (ch90C.filter (·.value == .nounRelativeClauseDominant)).length >
    ch90C.length * 9 / 10 := by decide

set_option maxRecDepth 4096 in
/-- Ch 60: "Highly differentiated" between genitives, adjectives, and relative
    clauses is the majority value. -/
theorem ch60_highlyDifferentiated_majority :
    (ch60.filter (·.value == .highlyDifferentiated)).length >
    ch60.length / 2 := by decide

set_option maxRecDepth 4096 in
/-- Ch 61: "Without marking" is the majority strategy for headless adjective
    phrases. -/
theorem ch61_withoutMarking_majority :
    (ch61.filter (·.value == .withoutMarking)).length >
    ch61.length / 2 := by decide

-- ============================================================================
-- Fragment sample: per-language `LanguageProfile`s for cross-linguistic claims
-- ============================================================================
-- Per the Fragments-as-typology-endpoint architecture: samples are built from
-- per-language `LanguageProfile` values rather than constructed inline. The
-- source-of-truth chain:
--   WALS → Core.Typology.{WordOrder,Adposition} ISO lookups
--        → LanguageProfile.{ofWALS, withWordOrderFromWALS, withAdpositionFromWALS}
--        → Fragments.{Lang}.typology  (when overrides/morphology exist)
--        → Phenomena.WordOrder.Typology.fragmentSample.
--
-- Languages with hand-coded `morphProfile` overrides live in `Fragments/`; pure-
-- WALS languages are inlined as `Core.Typology.LanguageProfile.ofWALS` directly.

open Core.Typology (LanguageProfile) in
/-- Hand-verified sample of `LanguageProfile`s spanning the four major basic-
    order classes (SOV, SVO, VSO, plus a couple non-SVO order entries) with
    adposition data attested in WALS. Used for stating cross-linguistic
    Greenbergian universals; `Core.Typology.ImplicationalUniversal` is the
    corresponding API.

    Each entry's domain values come from WALS via ISO 639-3 lookup — see
    `LanguageProfile.ofWALS` and the per-domain `withXFromWALS` helpers. The
    five languages with Fragment files (English, Japanese, Mandarin, Korean,
    Arabic) bring along their hand-coded `morphProfile`; the remaining nine
    are inlined here because they carry no overrides. -/
def fragmentSample : Finset LanguageProfile :=
  -- Fragment-sourced (carry morphProfile overrides):
  { Fragments.English.typology     -- eng, SVO, prepositional
  , Fragments.Japanese.typology    -- jpn, SOV, postpositional
  , Fragments.Mandarin.typology    -- cmn, SVO, mixed adpositions
  , Fragments.Korean.typology      -- kor, SOV, postpositional
  , Fragments.Arabic.typology      -- arb, VSO, prepositional
  -- VSO + prepositional (Celtic):
  , LanguageProfile.ofWALS "cym" "Welsh"
  , LanguageProfile.ofWALS "gle" "Irish"
  -- Additional SOV + postpositional:
  , LanguageProfile.ofWALS "tur" "Turkish"
  , LanguageProfile.ofWALS "hin" "Hindi"
  , LanguageProfile.ofWALS "eus" "Basque"
  -- Additional SVO + prepositional:
  , LanguageProfile.ofWALS "rus" "Russian"
  , LanguageProfile.ofWALS "swh" "Swahili"
  , LanguageProfile.ofWALS "ind" "Indonesian"
  -- Object-initial / verb-final-object orders for shape diversity:
  , LanguageProfile.ofWALS "tzo" "Tzotzil"   -- VOS, prepositional
  , LanguageProfile.ofWALS "hix" "Hixkaryana" -- OVS, postpositional
  }

-- ============================================================================
-- Greenbergian implicational universals over `fragmentSample`
-- ============================================================================
-- @cite{greenberg-1963} stated 45 cross-linguistic implicational universals.
-- Two of the most cited concern adposition order:
--
--   U3: VSO languages are prepositional.
--   U4: SOV languages are postpositional (with overwhelming greater than chance frequency).
--
-- Below: predicates over `LanguageProfile`, then the universal claims as
-- `Core.Typology.ImplicationalUniversal` instances over `fragmentSample`. The
-- proofs decide a quotient over a 15-element `Finset` literal — bumping
-- `maxRecDepth` is the same idiom mathlib uses for similar `Finset.decide`
-- sites (see `Core/Typology/Universal.lean` for the discussion).

open Core.Typology (LanguageProfile ImplicationalUniversal)

/-- Language has WALS basic order VSO. -/
def isVSO (p : LanguageProfile) : Prop :=
  p.wordOrder.basicOrder = .vso

/-- Language has WALS basic order SOV. -/
def isSOV (p : LanguageProfile) : Prop :=
  p.wordOrder.basicOrder = .sov

/-- Language is classified as prepositional in WALS Ch 85. -/
def isPrepositional (p : LanguageProfile) : Prop :=
  p.adposition = some .prepositional

/-- Language is classified as postpositional in WALS Ch 85. -/
def isPostpositional (p : LanguageProfile) : Prop :=
  p.adposition = some .postpositional

instance : DecidablePred isVSO := fun p => by unfold isVSO; infer_instance
instance : DecidablePred isSOV := fun p => by unfold isSOV; infer_instance
instance : DecidablePred isPrepositional := fun p => by unfold isPrepositional; infer_instance
instance : DecidablePred isPostpositional := fun p => by unfold isPostpositional; infer_instance

set_option maxRecDepth 4096 in
/-- @cite{greenberg-1963} Universal 3: "Languages with dominant VSO order
    are always prepositional." Tested over `fragmentSample`; antecedent is
    triggered by Arabic, Welsh, Irish, all of which are prepositional. -/
theorem greenberg_universal_3 :
    ImplicationalUniversal isVSO isPrepositional fragmentSample := by
  decide

set_option maxRecDepth 4096 in
/-- @cite{greenberg-1963} Universal 4: "With overwhelmingly greater than
    chance frequency, languages with normal SOV order are postpositional."
    Tested over `fragmentSample`; antecedent triggers Japanese, Korean,
    Turkish, Hindi, and Basque — all postpositional in WALS. -/
theorem greenberg_universal_4 :
    ImplicationalUniversal isSOV isPostpositional fragmentSample := by
  decide

-- ============================================================================
-- Cross-chapter WALS consistency over `fragmentSample`
-- ============================================================================
-- Each `LanguageProfile` in `fragmentSample` derives its `basicOrder` (Ch 81),
-- `svOrder` (Ch 82), and `ovOrder` (Ch 83) by independent ISO 639-3 lookups
-- against WALS. The theorems below verify that those independent lookups agree
-- per language: e.g. WALS-Ch81-SOV implies WALS-Ch82-SV and WALS-Ch83-OV. They
-- test internal consistency of WALS at the per-language level for the curated
-- sample, not a typological claim.

set_option maxRecDepth 4096 in
/-- Every SOV-by-Ch81 language in `fragmentSample` is SV-by-Ch82 and OV-by-Ch83. -/
theorem sov_implies_sv_and_ov :
    ∀ p ∈ fragmentSample, p.wordOrder.basicOrder = .sov →
      p.wordOrder.svOrder = .sv ∧ p.wordOrder.ovOrder = .ov := by
  decide

set_option maxRecDepth 4096 in
/-- Every SVO-by-Ch81 language in `fragmentSample` is SV-by-Ch82 and VO-by-Ch83. -/
theorem svo_implies_sv_and_vo :
    ∀ p ∈ fragmentSample, p.wordOrder.basicOrder = .svo →
      p.wordOrder.svOrder = .sv ∧ p.wordOrder.ovOrder = .vo := by
  decide

set_option maxRecDepth 4096 in
/-- Every VSO-by-Ch81 language in `fragmentSample` is VS-by-Ch82 and VO-by-Ch83. -/
theorem vso_implies_vs_and_vo :
    ∀ p ∈ fragmentSample, p.wordOrder.basicOrder = .vso →
      p.wordOrder.svOrder = .vs ∧ p.wordOrder.ovOrder = .vo := by
  decide

set_option maxRecDepth 4096 in
/-- Every VOS-by-Ch81 language in `fragmentSample` is VS-by-Ch82 and VO-by-Ch83. -/
theorem vos_implies_vs_and_vo :
    ∀ p ∈ fragmentSample, p.wordOrder.basicOrder = .vos →
      p.wordOrder.svOrder = .vs ∧ p.wordOrder.ovOrder = .vo := by
  decide

set_option maxRecDepth 4096 in
/-- Every OV-by-Ch83 language in `fragmentSample` has Ch 81 basic order SOV
    or OVS (the two S-containing OV orders). -/
theorem ov_languages_are_sov_or_ovs :
    ∀ p ∈ fragmentSample, p.wordOrder.ovOrder = .ov →
      p.wordOrder.basicOrder = .sov ∨ p.wordOrder.basicOrder = .ovs := by
  decide

set_option maxRecDepth 4096 in
/-- Every VO-by-Ch83 language in `fragmentSample` has Ch 81 basic order SVO,
    VSO, or VOS. -/
theorem vo_languages_are_svo_vso_or_vos :
    ∀ p ∈ fragmentSample, p.wordOrder.ovOrder = .vo →
      p.wordOrder.basicOrder = .svo ∨ p.wordOrder.basicOrder = .vso ∨
      p.wordOrder.basicOrder = .vos := by
  decide

end Phenomena.WordOrder.Typology
