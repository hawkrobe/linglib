import Linglib.Core.Lexical.Word
import Linglib.Core.WALS.Features.F81A
import Linglib.Core.WALS.Features.F82A
import Linglib.Core.WALS.Features.F83A

/-!
# Word-Order Typology (@cite{dryer-haspelmath-2013} / WALS)
@cite{dryer-1992} @cite{dryer-haspelmath-2013} @cite{gibson-2025} @cite{greenberg-1963} @cite{derbyshire-1977} @cite{hale-1983}

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
  deriving Repr, DecidableEq, BEq

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
-- Per-Cell Verification (12 cells)
-- ============================================================================

-- Table 1 cells
example : voAdposition.hihi.count = 454 := by native_decide
example : voAdposition.hihf.count = 41 := by native_decide
example : voAdposition.hfhi.count = 14 := by native_decide
example : voAdposition.hfhf.count = 472 := by native_decide

-- Table 2 cells
example : voSubordinator.hihi.count = 302 := by native_decide
example : voSubordinator.hihf.count = 2 := by native_decide
example : voSubordinator.hfhi.count = 61 := by native_decide
example : voSubordinator.hfhf.count = 91 := by native_decide

-- Table 3 cells
example : voRelativeClause.hihi.count = 415 := by native_decide
example : voRelativeClause.hihf.count = 5 := by native_decide
example : voRelativeClause.hfhi.count = 113 := by native_decide
example : voRelativeClause.hfhf.count = 132 := by native_decide

-- ============================================================================
-- Harmonic vs Disharmonic: Per-Table Theorems
-- ============================================================================

/-- Table 1: harmonic (926) > disharmonic (55). -/
theorem voAdposition_harmonic_dominant :
    voAdposition.harmonicDominant = true := by native_decide

/-- Table 2: harmonic (393) > disharmonic (63). -/
theorem voSubordinator_harmonic_dominant :
    voSubordinator.harmonicDominant = true := by native_decide

/-- Table 3: harmonic (547) > disharmonic (118). -/
theorem voRelativeClause_harmonic_dominant :
    voRelativeClause.harmonicDominant = true := by native_decide

-- ============================================================================
-- The Head-Direction Generalization (@cite{greenberg-1963} / @cite{dryer-1992})
-- ============================================================================

/-- The head-direction generalization: across all three construction pairs,
    harmonic word-order pairings dominate.

    This is the core empirical observation that @cite{gibson-2025}
    argues DLM explains: consistent head direction keeps recursive spine
    dependencies local. -/
theorem head_direction_generalization :
    allTables.all CrossTab.harmonicDominant = true := by native_decide

-- ============================================================================
-- Harmonic cells are themselves diagonal
-- ============================================================================

/-- Harmonic cells have matching directions. -/
theorem hihi_is_harmonic : voAdposition.hihi.isHarmonic = true := by native_decide
theorem hfhf_is_harmonic : voAdposition.hfhf.isHarmonic = true := by native_decide

/-- Disharmonic cells have mismatched directions. -/
theorem hihf_is_disharmonic : voAdposition.hihf.isHarmonic = false := by native_decide
theorem hfhi_is_disharmonic : voAdposition.hfhi.isHarmonic = false := by native_decide

-- ============================================================================
-- Totals
-- ============================================================================

/-- Table 1 total: 981 languages. -/
example : voAdposition.totalCount = 981 := by native_decide

/-- Table 2 total: 456 languages. -/
example : voSubordinator.totalCount = 456 := by native_decide

/-- Table 3 total: 665 languages. -/
example : voRelativeClause.totalCount = 665 := by native_decide

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
  deriving Repr, DecidableEq, BEq

/-- All single-word exceptions from Gibson Table 4. -/
def singleWordExceptions : List SingleWordException :=
  [.adjN, .demN, .intensAdj, .negVerb]

/-- These exceptions all involve dependents that are typically single words
    (leaves in the dependency tree), not recursive phrases. -/
def isSingleWordDependent : SingleWordException → Bool
  | .adjN => true        -- adjectives are typically leaves
  | .demN => true        -- demonstratives are single words
  | .intensAdj => true   -- intensifiers like "very" are single words
  | .negVerb => true     -- negation markers are single words

theorem all_exceptions_single_word :
    singleWordExceptions.all isSingleWordDependent = true := by native_decide

-- ============================================================================
-- WALS Distribution Data — derived from generated modules
-- ============================================================================
-- Full per-language data lives in Core.WALS.Features.F{81A,82A,83A}.
-- Aggregate counts are derived from the generated data by filtering.

/-- Ch 81 total: 1376 languages. -/
theorem ch81_total : Core.WALS.F81A.allData.length = 1376 :=
  Core.WALS.F81A.total_count

/-- Ch 82 total: 1496 languages. -/
theorem ch82_total : Core.WALS.F82A.allData.length = 1496 :=
  Core.WALS.F82A.total_count

/-- Ch 83 total: 1518 languages. -/
theorem ch83_total : Core.WALS.F83A.allData.length = 1518 :=
  Core.WALS.F83A.total_count

-- ============================================================================
-- Chapter 81: Basic Order of Subject, Object, and Verb
-- ============================================================================

/-- WALS Ch 81: The six-way classification of basic constituent order.

    The "basic" order is determined by the dominant order in pragmatically
    neutral, declarative clauses with full NP arguments. Languages where no
    single order clearly dominates (e.g., free word-order languages like
    Warlpiri, or V2 languages like German where underlying order is debated)
    are classified as "no dominant order."

    Key finding: SOV and SVO together account for >76% of languages;
    object-initial orders (OVS + OSV) are vanishingly rare.
    This asymmetry is one of the most robust typological generalizations:
    subjects overwhelmingly precede objects. -/
inductive BasicOrder where
  | sov | svo | vso | vos | ovs | osv | noDominant
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Chapter 82: Order of Subject and Verb
-- ============================================================================

/-- WALS Ch 82: Binary classification of S-V order. -/
inductive SVOrder where
  | sv | vs | noDominant
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Chapter 83: Order of Object and Verb
-- ============================================================================

/-- WALS Ch 83: Binary classification of O-V order.

    The most theoretically significant binary parameter: whether the object
    precedes the verb (OV = head-final VP) or follows it (VO = head-initial VP).
    This single parameter correlates with adposition order, genitive order,
    relative clause order, and subordinator order — the head-direction
    generalization formalized in the cross-tabulations above. -/
inductive OVOrder where
  | ov | vo | noDominant
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Basic Order Language Profiles
-- ============================================================================

/-- A language's basic word-order profile across WALS Chapters 81--83.

    Pairing a language's 6-way basic order (Ch 81) with its binary S-V (Ch 82)
    and O-V (Ch 83) classifications enables cross-chapter consistency checks:
    e.g., an SOV language should have SV order and OV order. -/
structure BasicOrderProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Ch 81: basic order of S, O, V. -/
  basicOrder : BasicOrder
  /-- Ch 82: order of subject and verb. -/
  svOrder : SVOrder
  /-- Ch 83: order of object and verb. -/
  ovOrder : OVOrder
  /-- Notes on the word-order system. -/
  notes : String := ""
  deriving Repr

-- ---- SOV languages ----

/-- Japanese: rigid SOV with postpositions, relative clause before noun,
    genitive before noun. The canonical head-final language. -/
def japanese : BasicOrderProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , basicOrder := .sov
  , svOrder := .sv
  , ovOrder := .ov
  , notes := "Rigid SOV; canonical head-final" }

/-- Turkish: SOV with postpositions. Relatively free word order for
    pragmatic effects, but SOV is strongly dominant. -/
def turkish : BasicOrderProfile :=
  { language := "Turkish"
  , iso := "tur"
  , basicOrder := .sov
  , svOrder := .sv
  , ovOrder := .ov
  , notes := "SOV dominant; some pragmatic reordering" }

/-- Hindi-Urdu: SOV with postpositions. Word order is relatively flexible
    due to case marking, but SOV is the default neutral order. -/
def hindiUrdu : BasicOrderProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , basicOrder := .sov
  , svOrder := .sv
  , ovOrder := .ov
  , notes := "SOV default; case marking allows scrambling" }

/-- Korean: rigid SOV with postpositions, relative clause before noun.
    Very similar head-final profile to Japanese. -/
def korean : BasicOrderProfile :=
  { language := "Korean"
  , iso := "kor"
  , basicOrder := .sov
  , svOrder := .sv
  , ovOrder := .ov
  , notes := "Rigid SOV; head-final like Japanese" }

/-- Quechua (Southern): rigid SOV with postpositions, suffixal morphology.
    One of the most consistently head-final languages. -/
def quechua : BasicOrderProfile :=
  { language := "Quechua"
  , iso := "que"
  , basicOrder := .sov
  , svOrder := .sv
  , ovOrder := .ov
  , notes := "Rigid SOV; consistently head-final" }

/-- Basque: SOV with postpositions. Ergative-absolutive case system.
    Word order is flexible but SOV is the pragmatically neutral order. -/
def basque : BasicOrderProfile :=
  { language := "Basque"
  , iso := "eus"
  , basicOrder := .sov
  , svOrder := .sv
  , ovOrder := .ov
  , notes := "SOV dominant; ergative-absolutive case" }

-- ---- SVO languages ----

/-- English: rigid SVO with prepositions and relative clause after noun.
    The canonical head-initial language (among non-V-initial types). -/
def english : BasicOrderProfile :=
  { language := "English"
  , iso := "eng"
  , basicOrder := .svo
  , svOrder := .sv
  , ovOrder := .vo
  , notes := "Rigid SVO; canonical head-initial (non-V-initial)" }

/-- Mandarin Chinese: SVO with prepositions (mostly). Some constructions
    are head-final (relative clause before noun, some postpositions),
    making Mandarin a mixed-headedness language. -/
def mandarinChinese : BasicOrderProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , basicOrder := .svo
  , svOrder := .sv
  , ovOrder := .vo
  , notes := "SVO but mixed headedness; RelCl-N, some postpositions" }

/-- Russian: SVO as the pragmatically neutral order, but word order is
    relatively free due to rich case morphology. -/
def russian : BasicOrderProfile :=
  { language := "Russian"
  , iso := "rus"
  , basicOrder := .svo
  , svOrder := .sv
  , ovOrder := .vo
  , notes := "SVO dominant; case morphology allows scrambling" }

/-- Swahili: SVO with prepositions. Bantu language with rich verbal
    agreement that cross-references subject and object. -/
def swahili : BasicOrderProfile :=
  { language := "Swahili"
  , iso := "swh"
  , basicOrder := .svo
  , svOrder := .sv
  , ovOrder := .vo
  , notes := "SVO; rich verbal agreement cross-referencing S and O" }

/-- Indonesian: SVO with prepositions. Relatively rigid word order
    for an Austronesian language. -/
def indonesian : BasicOrderProfile :=
  { language := "Indonesian"
  , iso := "ind"
  , basicOrder := .svo
  , svOrder := .sv
  , ovOrder := .vo
  , notes := "SVO; rigid for an Austronesian language" }

-- ---- VSO languages ----

/-- Arabic (Modern Standard): VSO as the classical/formal basic order,
    though SVO is increasingly common in spoken varieties. -/
def arabicMSA : BasicOrderProfile :=
  { language := "Arabic (MSA)"
  , iso := "arb"
  , basicOrder := .vso
  , svOrder := .vs
  , ovOrder := .vo
  , notes := "VSO classical; SVO common in modern spoken varieties" }

/-- Irish: VSO with prepositions, relative clause after noun. Celtic
    languages are the canonical European VSO family. -/
def irish : BasicOrderProfile :=
  { language := "Irish"
  , iso := "gle"
  , basicOrder := .vso
  , svOrder := .vs
  , ovOrder := .vo
  , notes := "VSO; Celtic canonical VSO" }

/-- Tagalog: VSO / VOS (verb-initial with flexible S/O ordering).
    WALS classifies as VSO based on pragmatically neutral clauses.
    Philippine-type voice system complicates the S vs O distinction. -/
def tagalog : BasicOrderProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , basicOrder := .vso
  , svOrder := .vs
  , ovOrder := .vo
  , notes := "VSO; Philippine voice system complicates S/O identification" }

/-- Welsh: VSO with prepositions, relative clause after noun.
    Another Celtic VSO language. -/
def welsh : BasicOrderProfile :=
  { language := "Welsh"
  , iso := "cym"
  , basicOrder := .vso
  , svOrder := .vs
  , ovOrder := .vo
  , notes := "VSO; Celtic VSO like Irish" }

-- ---- VOS languages ----

/-- Malagasy: VOS with prepositions. The best-known VOS language,
    extensively studied in formal syntax. -/
def malagasy : BasicOrderProfile :=
  { language := "Malagasy"
  , iso := "mlg"
  , basicOrder := .vos
  , svOrder := .vs
  , ovOrder := .vo
  , notes := "VOS; Austronesian; extensively studied in formal syntax" }

/-- Tzotzil (Mayan): VOS basic order, common in the Mayan family. -/
def tzotzil : BasicOrderProfile :=
  { language := "Tzotzil"
  , iso := "tzo"
  , basicOrder := .vos
  , svOrder := .vs
  , ovOrder := .vo
  , notes := "VOS; Mayan family" }

-- ---- OVS languages ----

/-- Hixkaryana (Cariban; Brazil): the first language for which OVS basic
    order was convincingly demonstrated. This discovery
    refuted the earlier claim that OVS and OSV orders were unattested. -/
def hixkaryana : BasicOrderProfile :=
  { language := "Hixkaryana"
  , iso := "hix"
  , basicOrder := .ovs
  , svOrder := .vs
  , ovOrder := .ov
  , notes := "OVS; first demonstrated by Derbyshire (1977); Cariban" }

-- ---- No dominant order ----

/-- German: V2 in main clauses, SOV in embedded clauses. WALS classifies
    as SVO, but many syntacticians analyze the underlying order as SOV
    with V2 movement. The tension makes "no dominant order" defensible
    (though WALS itself codes German as SVO). -/
def germanV2 : BasicOrderProfile :=
  { language := "German"
  , iso := "deu"
  , basicOrder := .noDominant
  , svOrder := .sv
  , ovOrder := .noDominant
  , notes := "V2 main clauses, SOV embedded; WALS codes as SVO" }

/-- Warlpiri (Pama-Nyungan; Australia): radically free word order, with
    all six permutations of S, O, V attested in natural discourse.
    The canonical non-configurational language. -/
def warlpiri : BasicOrderProfile :=
  { language := "Warlpiri"
  , iso := "wbp"
  , basicOrder := .noDominant
  , svOrder := .noDominant
  , ovOrder := .noDominant
  , notes := "Radically free word order; canonical non-configurational (Hale 1983)" }

/-- All basic-order language profiles in the sample. -/
def basicOrderProfiles : List BasicOrderProfile :=
  [ japanese, turkish, hindiUrdu, korean, quechua, basque          -- SOV
  , english, mandarinChinese, russian, swahili, indonesian         -- SVO
  , arabicMSA, irish, tagalog, welsh                               -- VSO
  , malagasy, tzotzil                                              -- VOS
  , hixkaryana                                                     -- OVS
  , germanV2, warlpiri ]                                           -- noDominant

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Count of languages in a profile list with a given basic order. -/
def countByBasicOrder (langs : List BasicOrderProfile) (o : BasicOrder) : Nat :=
  (langs.filter (·.basicOrder == o)).length

/-- Count of languages in a profile list with a given S-V order. -/
def countBySVOrder (langs : List BasicOrderProfile) (o : SVOrder) : Nat :=
  (langs.filter (·.svOrder == o)).length

/-- Count of languages in a profile list with a given O-V order. -/
def countByOVOrder (langs : List BasicOrderProfile) (o : OVOrder) : Nat :=
  (langs.filter (·.ovOrder == o)).length

-- ============================================================================
-- Typological Generalizations
-- ============================================================================

-- Abbreviations for WALS filter counts
private abbrev ch81 := Core.WALS.F81A.allData
private abbrev ch82 := Core.WALS.F82A.allData
private abbrev ch83 := Core.WALS.F83A.allData

/-- Generalization 1: SOV is the most common basic order. -/
theorem sov_most_common :
    (ch81.filter (·.value == .sov)).length >
    (ch81.filter (·.value == .svo)).length := by native_decide

/-- Generalization 2: SOV + SVO together exceed 75% of all sampled languages. -/
theorem sov_svo_majority_overall :
    let sov := (ch81.filter (·.value == .sov)).length
    let svo := (ch81.filter (·.value == .svo)).length
    (sov + svo) * 4 > ch81.length * 3 := by native_decide

/-- Generalization 3: In Ch 83, OV slightly outnumbers VO. -/
theorem ov_dominant_ch83 :
    (ch83.filter (·.value == .ov)).length >
    (ch83.filter (·.value == .vo)).length := by native_decide

/-- Generalization 4: Subject-first orders (SOV + SVO) far outnumber
    verb-first orders (VSO + VOS). -/
theorem subject_first_dominant :
    let sf := (ch81.filter (·.value == .sov)).length +
              (ch81.filter (·.value == .svo)).length
    let vf := (ch81.filter (·.value == .vso)).length +
              (ch81.filter (·.value == .vos)).length
    sf > vf * 8 := by native_decide

/-- Generalization 5: Object-initial orders (OVS + OSV) are extremely
    rare — less than 2% of the sample. -/
theorem object_initial_rare :
    let oi := (ch81.filter (·.value == .ovs)).length +
              (ch81.filter (·.value == .osv)).length
    oi * 100 < ch81.length * 2 := by native_decide

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
    subj_before_obj > obj_before_subj * 28 := by native_decide

/-- Generalization 7: SV overwhelmingly dominates VS in Ch 82.
    SV languages outnumber VS languages by more than 5 to 1. -/
theorem sv_dominant :
    (ch82.filter (·.value == .sv)).length >
    (ch82.filter (·.value == .vs)).length * 5 := by native_decide

/-- Generalization 8: Cross-chapter consistency — all SOV languages in our
    sample have OV order (Ch 83) and SV order (Ch 82). -/
theorem sov_implies_sv_and_ov :
    let sovLangs := basicOrderProfiles.filter (·.basicOrder == .sov)
    sovLangs.all (λ p => p.svOrder == .sv && p.ovOrder == .ov) = true := by
  native_decide

/-- Cross-chapter consistency — all SVO languages in our sample have SV order
    (Ch 82) and VO order (Ch 83). -/
theorem svo_implies_sv_and_vo :
    let svoLangs := basicOrderProfiles.filter (·.basicOrder == .svo)
    svoLangs.all (λ p => p.svOrder == .sv && p.ovOrder == .vo) = true := by
  native_decide

/-- Cross-chapter consistency — all VSO languages in our sample have VS order
    (Ch 82) and VO order (Ch 83). -/
theorem vso_implies_vs_and_vo :
    let vsoLangs := basicOrderProfiles.filter (·.basicOrder == .vso)
    vsoLangs.all (λ p => p.svOrder == .vs && p.ovOrder == .vo) = true := by
  native_decide

/-- Cross-chapter consistency — all VOS languages in our sample have VS order
    (Ch 82) and VO order (Ch 83). -/
theorem vos_implies_vs_and_vo :
    let vosLangs := basicOrderProfiles.filter (·.basicOrder == .vos)
    vosLangs.all (λ p => p.svOrder == .vs && p.ovOrder == .vo) = true := by
  native_decide

/-- Generalization 9: All OV languages in our sample have basic order SOV
    or OVS (the two S-containing OV orders). -/
theorem ov_languages_are_sov_or_ovs :
    let ovLangs := basicOrderProfiles.filter (·.ovOrder == .ov)
    ovLangs.all (λ p => p.basicOrder == .sov || p.basicOrder == .ovs) = true := by
  native_decide

/-- All VO languages in our sample have basic order SVO, VSO, or VOS. -/
theorem vo_languages_are_svo_vso_or_vos :
    let voLangs := basicOrderProfiles.filter (·.ovOrder == .vo)
    voLangs.all (λ p =>
      p.basicOrder == .svo || p.basicOrder == .vso || p.basicOrder == .vos
    ) = true := by
  native_decide

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

-- SOV languages
theorem japanese_is_sov : japanese.basicOrder == .sov := by native_decide
theorem turkish_is_sov : turkish.basicOrder == .sov := by native_decide
theorem hindiUrdu_is_sov : hindiUrdu.basicOrder == .sov := by native_decide
theorem korean_is_sov : korean.basicOrder == .sov := by native_decide
theorem quechua_is_sov : quechua.basicOrder == .sov := by native_decide
theorem basque_is_sov : basque.basicOrder == .sov := by native_decide

-- SVO languages
theorem english_is_svo : english.basicOrder == .svo := by native_decide
theorem mandarin_is_svo : mandarinChinese.basicOrder == .svo := by native_decide
theorem russian_is_svo : russian.basicOrder == .svo := by native_decide
theorem swahili_is_svo : swahili.basicOrder == .svo := by native_decide
theorem indonesian_is_svo : indonesian.basicOrder == .svo := by native_decide

-- VSO languages
theorem arabic_is_vso : arabicMSA.basicOrder == .vso := by native_decide
theorem irish_is_vso : irish.basicOrder == .vso := by native_decide
theorem tagalog_is_vso : tagalog.basicOrder == .vso := by native_decide
theorem welsh_is_vso : welsh.basicOrder == .vso := by native_decide

-- VOS languages
theorem malagasy_is_vos : malagasy.basicOrder == .vos := by native_decide
theorem tzotzil_is_vos : tzotzil.basicOrder == .vos := by native_decide

-- OVS languages
theorem hixkaryana_is_ovs : hixkaryana.basicOrder == .ovs := by native_decide

-- No dominant order
theorem germanV2_no_dominant : germanV2.basicOrder == .noDominant := by native_decide
theorem warlpiri_no_dominant : warlpiri.basicOrder == .noDominant := by native_decide

-- ============================================================================
-- Sample Size
-- ============================================================================

/-- Number of languages in our basic-order profile sample. -/
theorem basic_order_sample_size : basicOrderProfiles.length = 20 := by native_decide

/-- Distribution of basic orders in our sample. -/
theorem sample_sov_count : countByBasicOrder basicOrderProfiles .sov = 6 := by native_decide
theorem sample_svo_count : countByBasicOrder basicOrderProfiles .svo = 5 := by native_decide
theorem sample_vso_count : countByBasicOrder basicOrderProfiles .vso = 4 := by native_decide
theorem sample_vos_count : countByBasicOrder basicOrderProfiles .vos = 2 := by native_decide
theorem sample_ovs_count : countByBasicOrder basicOrderProfiles .ovs = 1 := by native_decide
theorem sample_osv_count : countByBasicOrder basicOrderProfiles .osv = 0 := by native_decide
theorem sample_noDom_count : countByBasicOrder basicOrderProfiles .noDominant = 2 := by native_decide

-- ============================================================================
-- WALS Grounding: Profile values match generated WALS data
-- ============================================================================

/-- Convert WALS 81A value to our BasicOrder type. -/
private def fromWALS81A : Core.WALS.F81A.BasicWordOrder → BasicOrder
  | .sov => .sov | .svo => .svo | .vso => .vso
  | .vos => .vos | .ovs => .ovs | .osv => .osv
  | .noDominantOrder => .noDominant

/-- Convert WALS 82A value to our SVOrder type. -/
private def fromWALS82A : Core.WALS.F82A.SubjectVerbOrder → SVOrder
  | .sv => .sv | .vs => .vs | .noDominantOrder => .noDominant

/-- Convert WALS 83A value to our OVOrder type. -/
private def fromWALS83A : Core.WALS.F83A.ObjectVerbOrder → OVOrder
  | .ov => .ov | .vo => .vo | .noDominantOrder => .noDominant

/-- For each profile whose language is in WALS Ch 81A, prove its basic order
    matches the WALS data. Languages not in the WALS sample (Malagasy, Quechua)
    are excluded — their profiles are ungrounded assertions. -/

-- Ch 81A grounding (basic word order)
theorem japanese_order_wals :
    (Core.WALS.F81A.lookup "jpn").map (fromWALS81A ·.value) = some japanese.basicOrder := by
  native_decide
theorem turkish_order_wals :
    (Core.WALS.F81A.lookup "tur").map (fromWALS81A ·.value) = some turkish.basicOrder := by
  native_decide
theorem hindiUrdu_order_wals :
    (Core.WALS.F81A.lookup "hin").map (fromWALS81A ·.value) = some hindiUrdu.basicOrder := by
  native_decide
theorem korean_order_wals :
    (Core.WALS.F81A.lookup "kor").map (fromWALS81A ·.value) = some korean.basicOrder := by
  native_decide
theorem basque_order_wals :
    (Core.WALS.F81A.lookup "bsq").map (fromWALS81A ·.value) = some basque.basicOrder := by
  native_decide
theorem english_order_wals :
    (Core.WALS.F81A.lookup "eng").map (fromWALS81A ·.value) = some english.basicOrder := by
  native_decide
theorem mandarin_order_wals :
    (Core.WALS.F81A.lookup "mnd").map (fromWALS81A ·.value) = some mandarinChinese.basicOrder := by
  native_decide
theorem russian_order_wals :
    (Core.WALS.F81A.lookup "rus").map (fromWALS81A ·.value) = some russian.basicOrder := by
  native_decide
theorem swahili_order_wals :
    (Core.WALS.F81A.lookup "swa").map (fromWALS81A ·.value) = some swahili.basicOrder := by
  native_decide
theorem indonesian_order_wals :
    (Core.WALS.F81A.lookup "ind").map (fromWALS81A ·.value) = some indonesian.basicOrder := by
  native_decide
theorem arabic_order_wals :
    (Core.WALS.F81A.lookup "ams").map (fromWALS81A ·.value) = some arabicMSA.basicOrder := by
  native_decide
theorem irish_order_wals :
    (Core.WALS.F81A.lookup "iri").map (fromWALS81A ·.value) = some irish.basicOrder := by
  native_decide
theorem tagalog_order_wals :
    (Core.WALS.F81A.lookup "tag").map (fromWALS81A ·.value) = some tagalog.basicOrder := by
  native_decide
theorem welsh_order_wals :
    (Core.WALS.F81A.lookup "wec").map (fromWALS81A ·.value) = some welsh.basicOrder := by
  native_decide
theorem tzotzil_order_wals :
    (Core.WALS.F81A.lookup "tzo").map (fromWALS81A ·.value) = some tzotzil.basicOrder := by
  native_decide
theorem hixkaryana_order_wals :
    (Core.WALS.F81A.lookup "hix").map (fromWALS81A ·.value) = some hixkaryana.basicOrder := by
  native_decide
theorem german_order_wals :
    (Core.WALS.F81A.lookup "ger").map (fromWALS81A ·.value) = some germanV2.basicOrder := by
  native_decide
theorem warlpiri_order_wals :
    (Core.WALS.F81A.lookup "wrl").map (fromWALS81A ·.value) = some warlpiri.basicOrder := by
  native_decide

-- Ch 82A grounding (subject-verb order)
theorem japanese_sv_wals :
    (Core.WALS.F82A.lookup "jpn").map (fromWALS82A ·.value) = some japanese.svOrder := by
  native_decide
theorem english_sv_wals :
    (Core.WALS.F82A.lookup "eng").map (fromWALS82A ·.value) = some english.svOrder := by
  native_decide
theorem arabic_sv_wals :
    (Core.WALS.F82A.lookup "ams").map (fromWALS82A ·.value) = some arabicMSA.svOrder := by
  native_decide
theorem hixkaryana_sv_wals :
    (Core.WALS.F82A.lookup "hix").map (fromWALS82A ·.value) = some hixkaryana.svOrder := by
  native_decide
theorem warlpiri_sv_wals :
    (Core.WALS.F82A.lookup "wrl").map (fromWALS82A ·.value) = some warlpiri.svOrder := by
  native_decide

-- Ch 83A grounding (object-verb order)
theorem japanese_ov_wals :
    (Core.WALS.F83A.lookup "jpn").map (fromWALS83A ·.value) = some japanese.ovOrder := by
  native_decide
theorem english_ov_wals :
    (Core.WALS.F83A.lookup "eng").map (fromWALS83A ·.value) = some english.ovOrder := by
  native_decide
theorem german_ov_wals :
    (Core.WALS.F83A.lookup "ger").map (fromWALS83A ·.value) = some germanV2.ovOrder := by
  native_decide
theorem warlpiri_ov_wals :
    (Core.WALS.F83A.lookup "wrl").map (fromWALS83A ·.value) = some warlpiri.ovOrder := by
  native_decide

end Phenomena.WordOrder.Typology
