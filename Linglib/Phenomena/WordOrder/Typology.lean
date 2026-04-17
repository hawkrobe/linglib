import Linglib.Core.Lexical.Word
import Linglib.Core.WALS.Features.F81A
import Linglib.Core.WALS.Features.F82A
import Linglib.Core.WALS.Features.F83A
import Linglib.Core.WALS.Features.F84A
import Linglib.Core.WALS.Features.F85A
import Linglib.Core.WALS.Features.F86A
import Linglib.Core.WALS.Features.F87A
import Linglib.Core.WALS.Features.F88A
import Linglib.Core.WALS.Features.F89A
import Linglib.Core.WALS.Features.F90A
import Linglib.Core.WALS.Features.F91A
import Linglib.Core.WALS.Features.F94A
import Linglib.Core.WALS.Features.F95A
import Linglib.Core.WALS.Features.F96A
import Linglib.Core.WALS.Features.F97A
import Linglib.Core.WALS.Features.F81B
import Linglib.Core.WALS.Features.F90B
import Linglib.Core.WALS.Features.F90C
import Linglib.Core.WALS.Features.F90D
import Linglib.Core.WALS.Features.F90E
import Linglib.Core.WALS.Features.F90F
import Linglib.Core.WALS.Features.F90G
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
-- Per-Cell Verification (12 cells)
-- ============================================================================

-- Table 1 cells
example : voAdposition.hihi.count = 454 := by decide
example : voAdposition.hihf.count = 41 := by decide
example : voAdposition.hfhi.count = 14 := by decide
example : voAdposition.hfhf.count = 472 := by decide

-- Table 2 cells
example : voSubordinator.hihi.count = 302 := by decide
example : voSubordinator.hihf.count = 2 := by decide
example : voSubordinator.hfhi.count = 61 := by decide
example : voSubordinator.hfhf.count = 91 := by decide

-- Table 3 cells
example : voRelativeClause.hihi.count = 415 := by decide
example : voRelativeClause.hihf.count = 5 := by decide
example : voRelativeClause.hfhi.count = 113 := by decide
example : voRelativeClause.hfhf.count = 132 := by decide

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

set_option maxRecDepth 4096 in
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
-- Totals
-- ============================================================================

/-- Table 1 total: 981 languages. -/
example : voAdposition.totalCount = 981 := by decide

/-- Table 2 total: 456 languages. -/
example : voSubordinator.totalCount = 456 := by decide

/-- Table 3 total: 665 languages. -/
example : voRelativeClause.totalCount = 665 := by decide

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
def isSingleWordDependent : SingleWordException → Bool
  | .adjN => true        -- adjectives are typically leaves
  | .demN => true        -- demonstratives are single words
  | .intensAdj => true   -- intensifiers like "very" are single words
  | .negVerb => true     -- negation markers are single words

theorem all_exceptions_single_word :
    singleWordExceptions.all isSingleWordDependent = true := by decide

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
  deriving DecidableEq, Repr

-- ============================================================================
-- Chapter 82: Order of Subject and Verb
-- ============================================================================

/-- WALS Ch 82: Binary classification of S-V order. -/
inductive SVOrder where
  | sv | vs | noDominant
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
private abbrev ch84 := Core.WALS.F84A.allData
private abbrev ch85 := Core.WALS.F85A.allData
private abbrev ch86 := Core.WALS.F86A.allData
private abbrev ch87 := Core.WALS.F87A.allData
private abbrev ch88 := Core.WALS.F88A.allData
private abbrev ch89 := Core.WALS.F89A.allData
private abbrev ch90 := Core.WALS.F90A.allData
private abbrev ch91 := Core.WALS.F91A.allData
private abbrev ch94 := Core.WALS.F94A.allData
private abbrev ch95 := Core.WALS.F95A.allData
private abbrev ch96 := Core.WALS.F96A.allData
private abbrev ch97 := Core.WALS.F97A.allData
private abbrev ch81B := Core.WALS.F81B.allData
private abbrev ch90B := Core.WALS.F90B.allData
private abbrev ch90C := Core.WALS.F90C.allData
private abbrev ch90D := Core.WALS.F90D.allData
private abbrev ch90E := Core.WALS.F90E.allData
private abbrev ch90F := Core.WALS.F90F.allData
private abbrev ch90G := Core.WALS.F90G.allData
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

set_option maxRecDepth 4096 in
/-- Generalization 8: Cross-chapter consistency — all SOV languages in our
    sample have OV order (Ch 83) and SV order (Ch 82). -/
theorem sov_implies_sv_and_ov :
    let sovLangs := basicOrderProfiles.filter (·.basicOrder == .sov)
    sovLangs.all (λ p => p.svOrder == .sv && p.ovOrder == .ov) = true := by
  decide

set_option maxRecDepth 4096 in
/-- Cross-chapter consistency — all SVO languages in our sample have SV order
    (Ch 82) and VO order (Ch 83). -/
theorem svo_implies_sv_and_vo :
    let svoLangs := basicOrderProfiles.filter (·.basicOrder == .svo)
    svoLangs.all (λ p => p.svOrder == .sv && p.ovOrder == .vo) = true := by
  decide

set_option maxRecDepth 4096 in
/-- Cross-chapter consistency — all VSO languages in our sample have VS order
    (Ch 82) and VO order (Ch 83). -/
theorem vso_implies_vs_and_vo :
    let vsoLangs := basicOrderProfiles.filter (·.basicOrder == .vso)
    vsoLangs.all (λ p => p.svOrder == .vs && p.ovOrder == .vo) = true := by
  decide

set_option maxRecDepth 4096 in
/-- Cross-chapter consistency — all VOS languages in our sample have VS order
    (Ch 82) and VO order (Ch 83). -/
theorem vos_implies_vs_and_vo :
    let vosLangs := basicOrderProfiles.filter (·.basicOrder == .vos)
    vosLangs.all (λ p => p.svOrder == .vs && p.ovOrder == .vo) = true := by
  decide

set_option maxRecDepth 4096 in
/-- Generalization 9: All OV languages in our sample have basic order SOV
    or OVS (the two S-containing OV orders). -/
theorem ov_languages_are_sov_or_ovs :
    let ovLangs := basicOrderProfiles.filter (·.ovOrder == .ov)
    ovLangs.all (λ p => p.basicOrder == .sov || p.basicOrder == .ovs) = true := by
  decide

set_option maxRecDepth 4096 in
/-- All VO languages in our sample have basic order SVO, VSO, or VOS. -/
theorem vo_languages_are_svo_vso_or_vos :
    let voLangs := basicOrderProfiles.filter (·.ovOrder == .vo)
    voLangs.all (λ p =>
      p.basicOrder == .svo || p.basicOrder == .vso || p.basicOrder == .vos
    ) = true := by
  decide

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

-- SOV languages
theorem japanese_is_sov : japanese.basicOrder == .sov := by decide
theorem turkish_is_sov : turkish.basicOrder == .sov := by decide
theorem hindiUrdu_is_sov : hindiUrdu.basicOrder == .sov := by decide
theorem korean_is_sov : korean.basicOrder == .sov := by decide
theorem quechua_is_sov : quechua.basicOrder == .sov := by decide
theorem basque_is_sov : basque.basicOrder == .sov := by decide

-- SVO languages
theorem english_is_svo : english.basicOrder == .svo := by decide
theorem mandarin_is_svo : mandarinChinese.basicOrder == .svo := by decide
theorem russian_is_svo : russian.basicOrder == .svo := by decide
theorem swahili_is_svo : swahili.basicOrder == .svo := by decide
theorem indonesian_is_svo : indonesian.basicOrder == .svo := by decide

-- VSO languages
theorem arabic_is_vso : arabicMSA.basicOrder == .vso := by decide
theorem irish_is_vso : irish.basicOrder == .vso := by decide
theorem tagalog_is_vso : tagalog.basicOrder == .vso := by decide
theorem welsh_is_vso : welsh.basicOrder == .vso := by decide

-- VOS languages
theorem malagasy_is_vos : malagasy.basicOrder == .vos := by decide
theorem tzotzil_is_vos : tzotzil.basicOrder == .vos := by decide

-- OVS languages
theorem hixkaryana_is_ovs : hixkaryana.basicOrder == .ovs := by decide

-- No dominant order
theorem germanV2_no_dominant : germanV2.basicOrder == .noDominant := by decide
theorem warlpiri_no_dominant : warlpiri.basicOrder == .noDominant := by decide

set_option maxRecDepth 4096 in
-- ============================================================================
-- Sample Size
-- ============================================================================

/-- Number of languages in our basic-order profile sample. -/
theorem basic_order_sample_size : basicOrderProfiles.length = 20 := by decide

set_option maxRecDepth 4096 in
/-- Distribution of basic orders in our sample. -/
theorem sample_sov_count : countByBasicOrder basicOrderProfiles .sov = 6 := by decide

set_option maxRecDepth 4096 in
theorem sample_svo_count : countByBasicOrder basicOrderProfiles .svo = 5 := by decide

set_option maxRecDepth 4096 in
theorem sample_vso_count : countByBasicOrder basicOrderProfiles .vso = 4 := by decide

set_option maxRecDepth 4096 in
theorem sample_vos_count : countByBasicOrder basicOrderProfiles .vos = 2 := by decide

set_option maxRecDepth 4096 in
theorem sample_ovs_count : countByBasicOrder basicOrderProfiles .ovs = 1 := by decide

set_option maxRecDepth 4096 in
theorem sample_osv_count : countByBasicOrder basicOrderProfiles .osv = 0 := by decide

set_option maxRecDepth 4096 in
theorem sample_noDom_count : countByBasicOrder basicOrderProfiles .noDominant = 2 := by decide

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

set_option maxRecDepth 4096 in
/-- For each profile whose language is in WALS Ch 81A, prove its basic order
    matches the WALS data. Languages not in the WALS sample (Malagasy, Quechua)
    are excluded — their profiles are ungrounded assertions. -/

-- Ch 81A grounding (basic word order)
theorem japanese_order_wals :
    (Core.WALS.F81A.lookup "jpn").map (fromWALS81A ·.value) = some japanese.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem turkish_order_wals :
    (Core.WALS.F81A.lookup "tur").map (fromWALS81A ·.value) = some turkish.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_order_wals :
    (Core.WALS.F81A.lookup "hin").map (fromWALS81A ·.value) = some hindiUrdu.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem korean_order_wals :
    (Core.WALS.F81A.lookup "kor").map (fromWALS81A ·.value) = some korean.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem basque_order_wals :
    (Core.WALS.F81A.lookup "bsq").map (fromWALS81A ·.value) = some basque.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem english_order_wals :
    (Core.WALS.F81A.lookup "eng").map (fromWALS81A ·.value) = some english.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem mandarin_order_wals :
    (Core.WALS.F81A.lookup "mnd").map (fromWALS81A ·.value) = some mandarinChinese.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem russian_order_wals :
    (Core.WALS.F81A.lookup "rus").map (fromWALS81A ·.value) = some russian.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem swahili_order_wals :
    (Core.WALS.F81A.lookup "swa").map (fromWALS81A ·.value) = some swahili.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem indonesian_order_wals :
    (Core.WALS.F81A.lookup "ind").map (fromWALS81A ·.value) = some indonesian.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem arabic_order_wals :
    (Core.WALS.F81A.lookup "ams").map (fromWALS81A ·.value) = some arabicMSA.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem irish_order_wals :
    (Core.WALS.F81A.lookup "iri").map (fromWALS81A ·.value) = some irish.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem tagalog_order_wals :
    (Core.WALS.F81A.lookup "tag").map (fromWALS81A ·.value) = some tagalog.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem welsh_order_wals :
    (Core.WALS.F81A.lookup "wec").map (fromWALS81A ·.value) = some welsh.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem tzotzil_order_wals :
    (Core.WALS.F81A.lookup "tzo").map (fromWALS81A ·.value) = some tzotzil.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem hixkaryana_order_wals :
    (Core.WALS.F81A.lookup "hix").map (fromWALS81A ·.value) = some hixkaryana.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem german_order_wals :
    (Core.WALS.F81A.lookup "ger").map (fromWALS81A ·.value) = some germanV2.basicOrder := by
  decide

set_option maxRecDepth 4096 in
theorem warlpiri_order_wals :
    (Core.WALS.F81A.lookup "wrl").map (fromWALS81A ·.value) = some warlpiri.basicOrder := by
  decide

set_option maxRecDepth 4096 in
-- Ch 82A grounding (subject-verb order)
theorem japanese_sv_wals :
    (Core.WALS.F82A.lookup "jpn").map (fromWALS82A ·.value) = some japanese.svOrder := by
  decide

set_option maxRecDepth 4096 in
theorem english_sv_wals :
    (Core.WALS.F82A.lookup "eng").map (fromWALS82A ·.value) = some english.svOrder := by
  decide

set_option maxRecDepth 4096 in
theorem arabic_sv_wals :
    (Core.WALS.F82A.lookup "ams").map (fromWALS82A ·.value) = some arabicMSA.svOrder := by
  decide

set_option maxRecDepth 4096 in
theorem hixkaryana_sv_wals :
    (Core.WALS.F82A.lookup "hix").map (fromWALS82A ·.value) = some hixkaryana.svOrder := by
  decide

set_option maxRecDepth 4096 in
theorem warlpiri_sv_wals :
    (Core.WALS.F82A.lookup "wrl").map (fromWALS82A ·.value) = some warlpiri.svOrder := by
  decide

set_option maxRecDepth 4096 in
-- Ch 83A grounding (object-verb order)
theorem japanese_ov_wals :
    (Core.WALS.F83A.lookup "jpn").map (fromWALS83A ·.value) = some japanese.ovOrder := by
  decide

set_option maxRecDepth 4096 in
theorem english_ov_wals :
    (Core.WALS.F83A.lookup "eng").map (fromWALS83A ·.value) = some english.ovOrder := by
  decide

set_option maxRecDepth 4096 in
theorem german_ov_wals :
    (Core.WALS.F83A.lookup "ger").map (fromWALS83A ·.value) = some germanV2.ovOrder := by
  decide

set_option maxRecDepth 4096 in
theorem warlpiri_ov_wals :
    (Core.WALS.F83A.lookup "wrl").map (fromWALS83A ·.value) = some warlpiri.ovOrder := by
  decide

-- ============================================================================
-- Chapter 84: Order of Object, Oblique, and Verb
-- ============================================================================

/-- Ch 84 total: 500 languages. -/
theorem ch84_total : ch84.length = 500 :=
  Core.WALS.F84A.total_count

/-- Convert WALS 84A value to a pair of head-direction options for O-V and X-V.
    The six-way classification encodes relative order of Object (O), Oblique (X),
    and Verb (V). Returns `none` for "no dominant order" since no single direction
    can be assigned. -/
private def fromWALS84A : Core.WALS.F84A.ObjectObliqueVerbOrder → Option (OVOrder × OVOrder)
  | .vox => some (.vo, .vo)   -- V before both O and X
  | .xvo => some (.vo, .vo)   -- X before V, V before O (both VO-ish)
  | .xov => some (.ov, .ov)   -- X before O before V (both OV-ish)
  | .oxv => some (.ov, .ov)   -- O before X before V (both OV-ish)
  | .ovx => some (.ov, .vo)   -- O before V, V before X (mixed)
  | .noDominantOrder => none

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 84
theorem ch84_count_vox :
    (ch84.filter (·.value == .vox)).length = 210 := by decide

set_option maxRecDepth 4096 in
theorem ch84_count_xov :
    (ch84.filter (·.value == .xov)).length = 48 := by decide

set_option maxRecDepth 4096 in
theorem ch84_count_ovx :
    (ch84.filter (·.value == .ovx)).length = 45 := by decide

set_option maxRecDepth 4096 in
theorem ch84_count_oxv :
    (ch84.filter (·.value == .oxv)).length = 27 := by decide

set_option maxRecDepth 4096 in
theorem ch84_count_xvo :
    (ch84.filter (·.value == .xvo)).length = 3 := by decide

set_option maxRecDepth 4096 in
theorem ch84_count_noDominantOrder :
    (ch84.filter (·.value == .noDominantOrder)).length = 167 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 84A
-- Note: Hindi, Korean, Russian, Swahili, Tagalog are absent from Ch 84A.
theorem english_ch84 :
    (Core.WALS.F84A.lookup "eng").map (·.value) = some .vox := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch84 :
    (Core.WALS.F84A.lookup "jpn").map (·.value) = some .xov := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch84 :
    (Core.WALS.F84A.lookup "tur").map (·.value) = some .xov := by decide

set_option maxRecDepth 4096 in
theorem basque_ch84 :
    (Core.WALS.F84A.lookup "bsq").map (·.value) = some .xov := by decide

set_option maxRecDepth 4096 in
theorem mandarin_ch84 :
    (Core.WALS.F84A.lookup "mnd").map (·.value) = some .xvo := by decide

set_option maxRecDepth 4096 in
theorem arabic_ch84 :
    (Core.WALS.F84A.lookup "ams").map (·.value) = some .vox := by decide

set_option maxRecDepth 4096 in
theorem irish_ch84 :
    (Core.WALS.F84A.lookup "iri").map (·.value) = some .vox := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch84 :
    (Core.WALS.F84A.lookup "ind").map (·.value) = some .vox := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch84 :
    (Core.WALS.F84A.lookup "mal").map (·.value) = some .vox := by decide

set_option maxRecDepth 4096 in
theorem tzotzil_ch84 :
    (Core.WALS.F84A.lookup "tzo").map (·.value) = some .vox := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch84 :
    (Core.WALS.F84A.lookup "hix").map (·.value) = some .ovx := by decide

set_option maxRecDepth 4096 in
theorem german_ch84 :
    (Core.WALS.F84A.lookup "ger").map (·.value) = some .noDominantOrder := by decide

set_option maxRecDepth 4096 in
theorem welsh_ch84 :
    (Core.WALS.F84A.lookup "wel").map (·.value) = some .vox := by decide

set_option maxRecDepth 4096 in
theorem warlpiri_ch84 :
    (Core.WALS.F84A.lookup "wrl").map (·.value) = some .noDominantOrder := by decide

-- ============================================================================
-- Chapter 85: Order of Adposition and Noun Phrase
-- ============================================================================

/-- WALS Ch 85: Order of adposition and NP. Maps to HeadDirection:
    prepositions are head-initial, postpositions are head-final.
    Inpositions, "no adpositions", and "no dominant order" have no clean mapping. -/
private def fromWALS85A : Core.WALS.F85A.AdpositionNPOrder → Option HeadDirection
  | .prepositions => some .headInitial
  | .postpositions => some .headFinal
  | .inpositions => none
  | .noDominantOrder => none
  | .noAdpositions => none

/-- Ch 85 total: 1184 languages. -/
theorem ch85_total : ch85.length = 1184 :=
  Core.WALS.F85A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 85
theorem ch85_count_postpositions :
    (ch85.filter (·.value == .postpositions)).length = 577 := by decide

set_option maxRecDepth 4096 in
theorem ch85_count_prepositions :
    (ch85.filter (·.value == .prepositions)).length = 511 := by decide

set_option maxRecDepth 4096 in
theorem ch85_count_inpositions :
    (ch85.filter (·.value == .inpositions)).length = 8 := by decide

set_option maxRecDepth 4096 in
theorem ch85_count_noDominantOrder :
    (ch85.filter (·.value == .noDominantOrder)).length = 58 := by decide

set_option maxRecDepth 4096 in
theorem ch85_count_noAdpositions :
    (ch85.filter (·.value == .noAdpositions)).length = 30 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 85A
-- Note: Warlpiri is absent from Ch 85A.
theorem english_ch85 :
    (Core.WALS.F85A.lookup "eng").map (·.value) = some .prepositions := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch85 :
    (Core.WALS.F85A.lookup "jpn").map (·.value) = some .postpositions := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch85 :
    (Core.WALS.F85A.lookup "tur").map (·.value) = some .postpositions := by decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_ch85 :
    (Core.WALS.F85A.lookup "hin").map (·.value) = some .postpositions := by decide

set_option maxRecDepth 4096 in
theorem korean_ch85 :
    (Core.WALS.F85A.lookup "kor").map (·.value) = some .postpositions := by decide

set_option maxRecDepth 4096 in
theorem basque_ch85 :
    (Core.WALS.F85A.lookup "bsq").map (·.value) = some .postpositions := by decide

set_option maxRecDepth 4096 in
-- Mandarin is "no dominant order" in Ch 85A (mixed pre/postpositions)
theorem mandarin_ch85 :
    (Core.WALS.F85A.lookup "mnd").map (·.value) = some .noDominantOrder := by decide

set_option maxRecDepth 4096 in
theorem russian_ch85 :
    (Core.WALS.F85A.lookup "rus").map (·.value) = some .prepositions := by decide

set_option maxRecDepth 4096 in
theorem swahili_ch85 :
    (Core.WALS.F85A.lookup "swa").map (·.value) = some .prepositions := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch85 :
    (Core.WALS.F85A.lookup "ind").map (·.value) = some .prepositions := by decide

set_option maxRecDepth 4096 in
theorem arabic_ch85 :
    (Core.WALS.F85A.lookup "ams").map (·.value) = some .prepositions := by decide

set_option maxRecDepth 4096 in
theorem irish_ch85 :
    (Core.WALS.F85A.lookup "iri").map (·.value) = some .prepositions := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch85 :
    (Core.WALS.F85A.lookup "mal").map (·.value) = some .prepositions := by decide

set_option maxRecDepth 4096 in
theorem tzotzil_ch85 :
    (Core.WALS.F85A.lookup "tzo").map (·.value) = some .prepositions := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch85 :
    (Core.WALS.F85A.lookup "hix").map (·.value) = some .postpositions := by decide

set_option maxRecDepth 4096 in
theorem welsh_ch85 :
    (Core.WALS.F85A.lookup "wel").map (·.value) = some .prepositions := by decide

set_option maxRecDepth 4096 in
theorem german_ch85 :
    (Core.WALS.F85A.lookup "ger").map (·.value) = some .prepositions := by decide

-- ============================================================================
-- Chapter 86: Order of Genitive and Noun
-- ============================================================================

/-- WALS Ch 86: Genitive-Noun vs Noun-Genitive order.
    Maps to HeadDirection: Gen-N is head-final (possessor precedes head noun),
    N-Gen is head-initial (head noun precedes possessor). -/
private def fromWALS86A : Core.WALS.F86A.GenitiveNounOrder → Option HeadDirection
  | .genitiveNoun => some .headFinal
  | .nounGenitive => some .headInitial
  | .noDominantOrder => none

/-- Ch 86 total: 1249 languages. -/
theorem ch86_total : ch86.length = 1249 :=
  Core.WALS.F86A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 86
theorem ch86_count_genitiveNoun :
    (ch86.filter (·.value == .genitiveNoun)).length = 685 := by decide

set_option maxRecDepth 4096 in
theorem ch86_count_nounGenitive :
    (ch86.filter (·.value == .nounGenitive)).length = 468 := by decide

set_option maxRecDepth 4096 in
theorem ch86_count_noDominantOrder :
    (ch86.filter (·.value == .noDominantOrder)).length = 96 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 86A
-- Note: Warlpiri is absent from Ch 86A.
theorem japanese_ch86 :
    (Core.WALS.F86A.lookup "jpn").map (·.value) = some .genitiveNoun := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch86 :
    (Core.WALS.F86A.lookup "tur").map (·.value) = some .genitiveNoun := by decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_ch86 :
    (Core.WALS.F86A.lookup "hin").map (·.value) = some .genitiveNoun := by decide

set_option maxRecDepth 4096 in
theorem korean_ch86 :
    (Core.WALS.F86A.lookup "kor").map (·.value) = some .genitiveNoun := by decide

set_option maxRecDepth 4096 in
theorem basque_ch86 :
    (Core.WALS.F86A.lookup "bsq").map (·.value) = some .genitiveNoun := by decide

set_option maxRecDepth 4096 in
-- English is "no dominant order" in Ch 86A (both "John's book" and "book of John")
theorem english_ch86 :
    (Core.WALS.F86A.lookup "eng").map (·.value) = some .noDominantOrder := by decide

set_option maxRecDepth 4096 in
theorem mandarin_ch86 :
    (Core.WALS.F86A.lookup "mnd").map (·.value) = some .genitiveNoun := by decide

set_option maxRecDepth 4096 in
theorem russian_ch86 :
    (Core.WALS.F86A.lookup "rus").map (·.value) = some .nounGenitive := by decide

set_option maxRecDepth 4096 in
theorem swahili_ch86 :
    (Core.WALS.F86A.lookup "swa").map (·.value) = some .nounGenitive := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch86 :
    (Core.WALS.F86A.lookup "ind").map (·.value) = some .nounGenitive := by decide

set_option maxRecDepth 4096 in
theorem arabic_ch86 :
    (Core.WALS.F86A.lookup "ams").map (·.value) = some .nounGenitive := by decide

set_option maxRecDepth 4096 in
theorem irish_ch86 :
    (Core.WALS.F86A.lookup "iri").map (·.value) = some .nounGenitive := by decide

set_option maxRecDepth 4096 in
theorem tagalog_ch86 :
    (Core.WALS.F86A.lookup "tag").map (·.value) = some .nounGenitive := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch86 :
    (Core.WALS.F86A.lookup "mal").map (·.value) = some .nounGenitive := by decide

set_option maxRecDepth 4096 in
theorem tzotzil_ch86 :
    (Core.WALS.F86A.lookup "tzo").map (·.value) = some .nounGenitive := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch86 :
    (Core.WALS.F86A.lookup "hix").map (·.value) = some .genitiveNoun := by decide

set_option maxRecDepth 4096 in
theorem welsh_ch86 :
    (Core.WALS.F86A.lookup "wel").map (·.value) = some .nounGenitive := by decide

set_option maxRecDepth 4096 in
theorem german_ch86 :
    (Core.WALS.F86A.lookup "ger").map (·.value) = some .nounGenitive := by decide

-- ============================================================================
-- Chapter 87: Order of Adjective and Noun
-- ============================================================================

/-- WALS Ch 87: Adjective-Noun vs Noun-Adjective order.
    Maps to HeadDirection: Adj-N is head-final (modifier precedes head),
    N-Adj is head-initial (head precedes modifier).
    "No dominant order" and "only internally-headed relative clauses" map to none. -/
private def fromWALS87A : Core.WALS.F87A.AdjectiveNounOrder → Option HeadDirection
  | .adjectiveNoun => some .headFinal
  | .nounAdjective => some .headInitial
  | .noDominantOrder => none
  | .onlyInternallyHeadedRelativeClauses => none

/-- Ch 87 total: 1367 languages. -/
theorem ch87_total : ch87.length = 1367 :=
  Core.WALS.F87A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 87
theorem ch87_count_adjectiveNoun :
    (ch87.filter (·.value == .adjectiveNoun)).length = 373 := by decide

set_option maxRecDepth 4096 in
theorem ch87_count_nounAdjective :
    (ch87.filter (·.value == .nounAdjective)).length = 879 := by decide

set_option maxRecDepth 4096 in
theorem ch87_count_noDominantOrder :
    (ch87.filter (·.value == .noDominantOrder)).length = 110 := by decide

set_option maxRecDepth 4096 in
theorem ch87_count_onlyIHRC :
    (ch87.filter (·.value == .onlyInternallyHeadedRelativeClauses)).length = 5 := by decide

set_option maxRecDepth 8192 in
-- N-Adj order dominates cross-linguistically (one of Gibson's single-word exceptions)
theorem nounAdj_dominant_ch87 :
    (ch87.filter (·.value == .nounAdjective)).length >
    (ch87.filter (·.value == .adjectiveNoun)).length * 2 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 87A
-- Note: Warlpiri has Noun-Adjective despite being SOV (a single-word exception).
theorem english_ch87 :
    (Core.WALS.F87A.lookup "eng").map (·.value) = some .adjectiveNoun := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch87 :
    (Core.WALS.F87A.lookup "jpn").map (·.value) = some .adjectiveNoun := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch87 :
    (Core.WALS.F87A.lookup "tur").map (·.value) = some .adjectiveNoun := by decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_ch87 :
    (Core.WALS.F87A.lookup "hin").map (·.value) = some .adjectiveNoun := by decide

set_option maxRecDepth 4096 in
theorem korean_ch87 :
    (Core.WALS.F87A.lookup "kor").map (·.value) = some .adjectiveNoun := by decide

set_option maxRecDepth 4096 in
-- Basque has Noun-Adjective despite being SOV (a single-word exception)
theorem basque_ch87 :
    (Core.WALS.F87A.lookup "bsq").map (·.value) = some .nounAdjective := by decide

set_option maxRecDepth 4096 in
theorem mandarin_ch87 :
    (Core.WALS.F87A.lookup "mnd").map (·.value) = some .adjectiveNoun := by decide

set_option maxRecDepth 4096 in
theorem russian_ch87 :
    (Core.WALS.F87A.lookup "rus").map (·.value) = some .adjectiveNoun := by decide

set_option maxRecDepth 4096 in
theorem swahili_ch87 :
    (Core.WALS.F87A.lookup "swa").map (·.value) = some .nounAdjective := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch87 :
    (Core.WALS.F87A.lookup "ind").map (·.value) = some .nounAdjective := by decide

set_option maxRecDepth 4096 in
theorem arabic_ch87 :
    (Core.WALS.F87A.lookup "ams").map (·.value) = some .nounAdjective := by decide

set_option maxRecDepth 4096 in
theorem irish_ch87 :
    (Core.WALS.F87A.lookup "iri").map (·.value) = some .nounAdjective := by decide

set_option maxRecDepth 4096 in
-- Tagalog is "no dominant order" for Adj-N in Ch 87A
theorem tagalog_ch87 :
    (Core.WALS.F87A.lookup "tag").map (·.value) = some .noDominantOrder := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch87 :
    (Core.WALS.F87A.lookup "mal").map (·.value) = some .nounAdjective := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch87 :
    (Core.WALS.F87A.lookup "hix").map (·.value) = some .nounAdjective := by decide

set_option maxRecDepth 4096 in
theorem warlpiri_ch87 :
    (Core.WALS.F87A.lookup "wrl").map (·.value) = some .nounAdjective := by decide

set_option maxRecDepth 4096 in
theorem welsh_ch87 :
    (Core.WALS.F87A.lookup "wel").map (·.value) = some .nounAdjective := by decide

set_option maxRecDepth 4096 in
theorem german_ch87 :
    (Core.WALS.F87A.lookup "ger").map (·.value) = some .adjectiveNoun := by decide

-- ============================================================================
-- Chapter 88: Order of Demonstrative and Noun
-- ============================================================================

/-- WALS Ch 88: Demonstrative-Noun vs Noun-Demonstrative order.
    Maps to HeadDirection: Dem-N is head-final (modifier precedes head),
    N-Dem is head-initial (head precedes modifier).
    Affixal, "both sides", and "mixed" values map to none. -/
private def fromWALS88A : Core.WALS.F88A.DemonstrativeNounOrder → Option HeadDirection
  | .demonstrativeNoun => some .headFinal
  | .nounDemonstrative => some .headInitial
  | .demonstrativePrefix => none
  | .demonstrativeSuffix => none
  | .demonstrativeBeforeAndAfterNoun => none
  | .mixed => none

/-- Ch 88 total: 1225 languages. -/
theorem ch88_total : ch88.length = 1225 :=
  Core.WALS.F88A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 88
theorem ch88_count_demonstrativeNoun :
    (ch88.filter (·.value == .demonstrativeNoun)).length = 542 := by decide

set_option maxRecDepth 4096 in
theorem ch88_count_nounDemonstrative :
    (ch88.filter (·.value == .nounDemonstrative)).length = 562 := by decide

set_option maxRecDepth 4096 in
theorem ch88_count_demonstrativePrefix :
    (ch88.filter (·.value == .demonstrativePrefix)).length = 9 := by decide

set_option maxRecDepth 4096 in
theorem ch88_count_demonstrativeSuffix :
    (ch88.filter (·.value == .demonstrativeSuffix)).length = 28 := by decide

set_option maxRecDepth 4096 in
theorem ch88_count_demonstrativeBeforeAndAfterNoun :
    (ch88.filter (·.value == .demonstrativeBeforeAndAfterNoun)).length = 17 := by decide

set_option maxRecDepth 4096 in
theorem ch88_count_mixed :
    (ch88.filter (·.value == .mixed)).length = 67 := by decide

set_option maxRecDepth 8192 in
-- Dem-N vs N-Dem is roughly balanced (another single-word exception: demonstratives
-- are single words, so head direction is less predictive)
theorem demN_roughly_balanced_ch88 :
    let demN := (ch88.filter (·.value == .demonstrativeNoun)).length
    let nDem := (ch88.filter (·.value == .nounDemonstrative)).length
    demN * 10 > nDem * 9 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 88A
-- Note: Warlpiri, Hixkaryana are absent from Ch 88A.
theorem english_ch88 :
    (Core.WALS.F88A.lookup "eng").map (·.value) = some .demonstrativeNoun := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch88 :
    (Core.WALS.F88A.lookup "jpn").map (·.value) = some .demonstrativeNoun := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch88 :
    (Core.WALS.F88A.lookup "tur").map (·.value) = some .demonstrativeNoun := by decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_ch88 :
    (Core.WALS.F88A.lookup "hin").map (·.value) = some .demonstrativeNoun := by decide

set_option maxRecDepth 4096 in
theorem korean_ch88 :
    (Core.WALS.F88A.lookup "kor").map (·.value) = some .demonstrativeNoun := by decide

set_option maxRecDepth 4096 in
-- Basque has Noun-Demonstrative despite being SOV (a single-word exception)
theorem basque_ch88 :
    (Core.WALS.F88A.lookup "bsq").map (·.value) = some .nounDemonstrative := by decide

set_option maxRecDepth 4096 in
theorem mandarin_ch88 :
    (Core.WALS.F88A.lookup "mnd").map (·.value) = some .demonstrativeNoun := by decide

set_option maxRecDepth 4096 in
theorem russian_ch88 :
    (Core.WALS.F88A.lookup "rus").map (·.value) = some .demonstrativeNoun := by decide

set_option maxRecDepth 4096 in
theorem swahili_ch88 :
    (Core.WALS.F88A.lookup "swa").map (·.value) = some .nounDemonstrative := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch88 :
    (Core.WALS.F88A.lookup "ind").map (·.value) = some .nounDemonstrative := by decide

set_option maxRecDepth 4096 in
theorem arabic_ch88 :
    (Core.WALS.F88A.lookup "ams").map (·.value) = some .demonstrativeNoun := by decide

set_option maxRecDepth 4096 in
theorem irish_ch88 :
    (Core.WALS.F88A.lookup "iri").map (·.value) = some .nounDemonstrative := by decide

set_option maxRecDepth 4096 in
-- Tagalog is "mixed" in Ch 88A
theorem tagalog_ch88 :
    (Core.WALS.F88A.lookup "tag").map (·.value) = some .mixed := by decide

set_option maxRecDepth 4096 in
-- Malagasy is "demonstrative before and after noun" in Ch 88A
theorem malagasy_ch88 :
    (Core.WALS.F88A.lookup "mal").map (·.value) = some .demonstrativeBeforeAndAfterNoun := by
  decide

set_option maxRecDepth 4096 in
theorem welsh_ch88 :
    (Core.WALS.F88A.lookup "wel").map (·.value) = some .nounDemonstrative := by decide

set_option maxRecDepth 4096 in
theorem german_ch88 :
    (Core.WALS.F88A.lookup "ger").map (·.value) = some .demonstrativeNoun := by decide

-- ============================================================================
-- Chapter 89: Order of Numeral and Noun
-- ============================================================================

/-- WALS Ch 89: Numeral-Noun vs Noun-Numeral order.
    Maps to HeadDirection: Num-N is head-final (modifier precedes head),
    N-Num is head-initial (head precedes modifier).
    "No dominant order" and "numeral only modifies verb" map to none. -/
private def fromWALS89A : Core.WALS.F89A.NumeralNounOrder → Option HeadDirection
  | .numeralNoun => some .headFinal
  | .nounNumeral => some .headInitial
  | .noDominantOrder => none
  | .numeralOnlyModifiesVerb => none

/-- Ch 89 total: 1154 languages. -/
theorem ch89_total : ch89.length = 1154 :=
  Core.WALS.F89A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 89
theorem ch89_count_numeralNoun :
    (ch89.filter (·.value == .numeralNoun)).length = 479 := by decide

set_option maxRecDepth 4096 in
theorem ch89_count_nounNumeral :
    (ch89.filter (·.value == .nounNumeral)).length = 608 := by decide

set_option maxRecDepth 4096 in
theorem ch89_count_noDominantOrder :
    (ch89.filter (·.value == .noDominantOrder)).length = 65 := by decide

set_option maxRecDepth 4096 in
theorem ch89_count_numeralOnlyModifiesVerb :
    (ch89.filter (·.value == .numeralOnlyModifiesVerb)).length = 2 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 89A
-- Note: Warlpiri is absent from Ch 89A.
-- Notably, most profile languages have Numeral-Noun regardless of basic order,
-- because numerals are typically single words (another single-word exception pattern).
theorem english_ch89 :
    (Core.WALS.F89A.lookup "eng").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch89 :
    (Core.WALS.F89A.lookup "jpn").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch89 :
    (Core.WALS.F89A.lookup "tur").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_ch89 :
    (Core.WALS.F89A.lookup "hin").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem korean_ch89 :
    (Core.WALS.F89A.lookup "kor").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem basque_ch89 :
    (Core.WALS.F89A.lookup "bsq").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem mandarin_ch89 :
    (Core.WALS.F89A.lookup "mnd").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem russian_ch89 :
    (Core.WALS.F89A.lookup "rus").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
-- Swahili has Noun-Numeral (head-initial, consistent with SVO)
theorem swahili_ch89 :
    (Core.WALS.F89A.lookup "swa").map (·.value) = some .nounNumeral := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch89 :
    (Core.WALS.F89A.lookup "ind").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem arabic_ch89 :
    (Core.WALS.F89A.lookup "ams").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem irish_ch89 :
    (Core.WALS.F89A.lookup "iri").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem tagalog_ch89 :
    (Core.WALS.F89A.lookup "tag").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
-- Malagasy has Noun-Numeral (head-initial, consistent with VOS)
theorem malagasy_ch89 :
    (Core.WALS.F89A.lookup "mal").map (·.value) = some .nounNumeral := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch89 :
    (Core.WALS.F89A.lookup "hix").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem welsh_ch89 :
    (Core.WALS.F89A.lookup "wel").map (·.value) = some .numeralNoun := by decide

set_option maxRecDepth 4096 in
theorem german_ch89 :
    (Core.WALS.F89A.lookup "ger").map (·.value) = some .numeralNoun := by decide

-- ============================================================================
-- Chapter 90: Order of Relative Clause and Noun
-- ============================================================================

/-- WALS Ch 90: Relative clause-Noun vs Noun-Relative clause order.
    Maps to HeadDirection: RelCl-N is head-final, N-RelCl is head-initial.
    Internally headed, correlative, adjoined, doubly headed, and mixed map to none. -/
private def fromWALS90A : Core.WALS.F90A.RelClauseNounOrder → Option HeadDirection
  | .relativeClauseNoun => some .headFinal
  | .nounRelativeClause => some .headInitial
  | .internallyHeaded => none
  | .correlative => none
  | .adjoined => none
  | .doublyHeaded => none
  | .mixed => none

/-- Ch 90 total: 824 languages. -/
theorem ch90_total : ch90.length = 824 :=
  Core.WALS.F90A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 90
theorem ch90_count_nounRelClause :
    (ch90.filter (·.value == .nounRelativeClause)).length = 579 := by decide

set_option maxRecDepth 4096 in
theorem ch90_count_relClauseNoun :
    (ch90.filter (·.value == .relativeClauseNoun)).length = 141 := by decide

set_option maxRecDepth 4096 in
theorem ch90_count_internallyHeaded :
    (ch90.filter (·.value == .internallyHeaded)).length = 24 := by decide

set_option maxRecDepth 4096 in
theorem ch90_count_correlative :
    (ch90.filter (·.value == .correlative)).length = 7 := by decide

set_option maxRecDepth 4096 in
theorem ch90_count_adjoined :
    (ch90.filter (·.value == .adjoined)).length = 8 := by decide

set_option maxRecDepth 4096 in
theorem ch90_count_doublyHeaded :
    (ch90.filter (·.value == .doublyHeaded)).length = 1 := by decide

set_option maxRecDepth 4096 in
theorem ch90_count_mixed :
    (ch90.filter (·.value == .mixed)).length = 64 := by decide

set_option maxRecDepth 8192 in
-- N-RelCl strongly dominates (relative clauses are recursive phrases, not single words)
theorem nounRelCl_dominant_ch90 :
    (ch90.filter (·.value == .nounRelativeClause)).length >
    (ch90.filter (·.value == .relativeClauseNoun)).length * 4 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 90A
-- Note: Arabic (MSA), Tzotzil are absent from Ch 90A.
theorem english_ch90 :
    (Core.WALS.F90A.lookup "eng").map (·.value) = some .nounRelativeClause := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch90 :
    (Core.WALS.F90A.lookup "jpn").map (·.value) = some .relativeClauseNoun := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch90 :
    (Core.WALS.F90A.lookup "tur").map (·.value) = some .relativeClauseNoun := by decide

set_option maxRecDepth 4096 in
-- Hindi uses correlative relative clauses (special strategy, not simply prenominal or postnominal)
theorem hindiUrdu_ch90 :
    (Core.WALS.F90A.lookup "hin").map (·.value) = some .correlative := by decide

set_option maxRecDepth 4096 in
theorem korean_ch90 :
    (Core.WALS.F90A.lookup "kor").map (·.value) = some .relativeClauseNoun := by decide

set_option maxRecDepth 4096 in
theorem basque_ch90 :
    (Core.WALS.F90A.lookup "bsq").map (·.value) = some .relativeClauseNoun := by decide

set_option maxRecDepth 4096 in
-- Mandarin has RelCl-N (prenominal relative clauses, head-final, disharmonic with SVO)
theorem mandarin_ch90 :
    (Core.WALS.F90A.lookup "mnd").map (·.value) = some .relativeClauseNoun := by decide

set_option maxRecDepth 4096 in
theorem russian_ch90 :
    (Core.WALS.F90A.lookup "rus").map (·.value) = some .nounRelativeClause := by decide

set_option maxRecDepth 4096 in
theorem swahili_ch90 :
    (Core.WALS.F90A.lookup "swa").map (·.value) = some .nounRelativeClause := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch90 :
    (Core.WALS.F90A.lookup "ind").map (·.value) = some .nounRelativeClause := by decide

set_option maxRecDepth 4096 in
theorem irish_ch90 :
    (Core.WALS.F90A.lookup "iri").map (·.value) = some .nounRelativeClause := by decide

set_option maxRecDepth 4096 in
theorem tagalog_ch90 :
    (Core.WALS.F90A.lookup "tag").map (·.value) = some .nounRelativeClause := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch90 :
    (Core.WALS.F90A.lookup "mal").map (·.value) = some .nounRelativeClause := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch90 :
    (Core.WALS.F90A.lookup "hix").map (·.value) = some .nounRelativeClause := by decide

set_option maxRecDepth 4096 in
-- Warlpiri uses adjoined relative clauses
theorem warlpiri_ch90 :
    (Core.WALS.F90A.lookup "wrl").map (·.value) = some .adjoined := by decide

set_option maxRecDepth 4096 in
theorem welsh_ch90 :
    (Core.WALS.F90A.lookup "wel").map (·.value) = some .nounRelativeClause := by decide

set_option maxRecDepth 4096 in
theorem german_ch90 :
    (Core.WALS.F90A.lookup "ger").map (·.value) = some .nounRelativeClause := by decide

-- ============================================================================
-- Chapter 91: Order of Degree Word and Adjective
-- ============================================================================

/-- WALS Ch 91: Degree word-Adjective vs Adjective-Degree word order.
    Maps to HeadDirection: DegW-Adj is head-final (modifier precedes head adjective
    in the functional sense), Adj-DegW is head-initial.
    "No dominant order" maps to none. -/
private def fromWALS91A : Core.WALS.F91A.OrderOfDegreeWordAndAdjective → Option HeadDirection
  | .degreeWordAdjective => some .headFinal
  | .adjectiveDegreeWord => some .headInitial
  | .noDominantOrder => none

/-- Ch 91 total: 481 languages. -/
theorem ch91_total : ch91.length = 481 :=
  Core.WALS.F91A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 91
theorem ch91_count_degreeWordAdjective :
    (ch91.filter (·.value == .degreeWordAdjective)).length = 227 := by decide

set_option maxRecDepth 4096 in
theorem ch91_count_adjectiveDegreeWord :
    (ch91.filter (·.value == .adjectiveDegreeWord)).length = 192 := by decide

set_option maxRecDepth 4096 in
theorem ch91_count_noDominantOrder :
    (ch91.filter (·.value == .noDominantOrder)).length = 62 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 91A
-- Note: Warlpiri, Irish, Tzotzil, Swahili, Tagalog, Malagasy are absent from Ch 91A.
theorem english_ch91 :
    (Core.WALS.F91A.lookup "eng").map (·.value) = some .degreeWordAdjective := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch91 :
    (Core.WALS.F91A.lookup "jpn").map (·.value) = some .degreeWordAdjective := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch91 :
    (Core.WALS.F91A.lookup "tur").map (·.value) = some .degreeWordAdjective := by decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_ch91 :
    (Core.WALS.F91A.lookup "hin").map (·.value) = some .degreeWordAdjective := by decide

set_option maxRecDepth 4096 in
theorem korean_ch91 :
    (Core.WALS.F91A.lookup "kor").map (·.value) = some .degreeWordAdjective := by decide

set_option maxRecDepth 4096 in
theorem basque_ch91 :
    (Core.WALS.F91A.lookup "bsq").map (·.value) = some .degreeWordAdjective := by decide

set_option maxRecDepth 4096 in
theorem mandarin_ch91 :
    (Core.WALS.F91A.lookup "mnd").map (·.value) = some .degreeWordAdjective := by decide

set_option maxRecDepth 4096 in
theorem russian_ch91 :
    (Core.WALS.F91A.lookup "rus").map (·.value) = some .degreeWordAdjective := by decide

set_option maxRecDepth 4096 in
-- Arabic has Adjective-Degree word order (Adj-DegW)
theorem arabic_ch91 :
    (Core.WALS.F91A.lookup "ams").map (·.value) = some .adjectiveDegreeWord := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch91 :
    (Core.WALS.F91A.lookup "hix").map (·.value) = some .adjectiveDegreeWord := by decide

set_option maxRecDepth 4096 in
-- Welsh is "no dominant order" for degree word and adjective
theorem welsh_ch91 :
    (Core.WALS.F91A.lookup "wel").map (·.value) = some .noDominantOrder := by decide

set_option maxRecDepth 4096 in
theorem german_ch91 :
    (Core.WALS.F91A.lookup "ger").map (·.value) = some .degreeWordAdjective := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch91 :
    (Core.WALS.F91A.lookup "ind").map (·.value) = some .degreeWordAdjective := by decide

-- ============================================================================
-- Chapter 94: Order of Adverbial Subordinator and Clause
-- ============================================================================

-- WALS Ch 94: Adverbial subordinator position relative to the clause.
-- No clean mapping to HeadDirection since this involves clause-level ordering
-- with multiple structural strategies (word vs suffix). We use the raw WALS type.

/-- Ch 94 total: 659 languages. -/
theorem ch94_total : ch94.length = 659 :=
  Core.WALS.F94A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 94
theorem ch94_count_initialSubordinatorWord :
    (ch94.filter (·.value == .initialSubordinatorWord)).length = 398 := by decide

set_option maxRecDepth 4096 in
theorem ch94_count_finalSubordinatorWord :
    (ch94.filter (·.value == .finalSubordinatorWord)).length = 96 := by decide

set_option maxRecDepth 4096 in
theorem ch94_count_internalSubordinatorWord :
    (ch94.filter (·.value == .internalSubordinatorWord)).length = 8 := by decide

set_option maxRecDepth 4096 in
theorem ch94_count_subordinatingSuffix :
    (ch94.filter (·.value == .subordinatingSuffix)).length = 64 := by decide

set_option maxRecDepth 4096 in
theorem ch94_count_mixed :
    (ch94.filter (·.value == .mixed)).length = 93 := by decide

set_option maxRecDepth 8192 in
-- Initial subordinator words are the most common strategy
theorem initial_subordinator_dominant_ch94 :
    (ch94.filter (·.value == .initialSubordinatorWord)).length >
    (ch94.filter (·.value == .finalSubordinatorWord)).length * 4 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 94A
-- Note: Basque, Japanese, Warlpiri, Mandarin are absent from Ch 94A.
theorem english_ch94 :
    (Core.WALS.F94A.lookup "eng").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_ch94 :
    (Core.WALS.F94A.lookup "hin").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem korean_ch94 :
    (Core.WALS.F94A.lookup "kor").map (·.value) =
    some .finalSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem russian_ch94 :
    (Core.WALS.F94A.lookup "rus").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem swahili_ch94 :
    (Core.WALS.F94A.lookup "swa").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch94 :
    (Core.WALS.F94A.lookup "ind").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem arabic_ch94 :
    (Core.WALS.F94A.lookup "ams").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem irish_ch94 :
    (Core.WALS.F94A.lookup "iri").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem tagalog_ch94 :
    (Core.WALS.F94A.lookup "tag").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch94 :
    (Core.WALS.F94A.lookup "mal").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem tzotzil_ch94 :
    (Core.WALS.F94A.lookup "tzo").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch94 :
    (Core.WALS.F94A.lookup "hix").map (·.value) =
    some .finalSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem welsh_ch94 :
    (Core.WALS.F94A.lookup "wel").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
theorem german_ch94 :
    (Core.WALS.F94A.lookup "ger").map (·.value) =
    some .initialSubordinatorWord := by decide

set_option maxRecDepth 4096 in
-- Turkish is "mixed" in Ch 94A (both subordinating suffixes and initial words)
theorem turkish_ch94 :
    (Core.WALS.F94A.lookup "tur").map (·.value) =
    some .mixed := by decide

-- ============================================================================
-- Chapter 95: Relationship between Order of OV and Adposition-NP
-- ============================================================================

-- WALS Ch 95: Cross-tabulation of O-V order with adposition order.
-- This is the "harmonic pair" test for VO/Prep vs OV/Postp.

/-- Ch 95 total: 1142 languages. -/
theorem ch95_total : ch95.length = 1142 :=
  Core.WALS.F95A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 95
theorem ch95_count_ovAndPostpositions :
    (ch95.filter (·.value == .ovAndPostpositions)).length = 472 := by decide

set_option maxRecDepth 4096 in
theorem ch95_count_ovAndPrepositions :
    (ch95.filter (·.value == .ovAndPrepositions)).length = 14 := by decide

set_option maxRecDepth 4096 in
theorem ch95_count_voAndPostpositions :
    (ch95.filter (·.value == .voAndPostpositions)).length = 42 := by decide

set_option maxRecDepth 4096 in
theorem ch95_count_voAndPrepositions :
    (ch95.filter (·.value == .voAndPrepositions)).length = 456 := by decide

set_option maxRecDepth 4096 in
theorem ch95_count_other :
    (ch95.filter (·.value == .other)).length = 158 := by decide

set_option maxRecDepth 8192 in
-- Harmonic pairs (OV+Postp, VO+Prep) vastly outnumber disharmonic (OV+Prep, VO+Postp)
theorem ch95_harmonic_dominant :
    let harmonic := (ch95.filter (·.value == .ovAndPostpositions)).length +
                    (ch95.filter (·.value == .voAndPrepositions)).length
    let disharmonic := (ch95.filter (·.value == .ovAndPrepositions)).length +
                       (ch95.filter (·.value == .voAndPostpositions)).length
    harmonic > disharmonic * 16 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 95A
theorem english_ch95 :
    (Core.WALS.F95A.lookup "eng").map (·.value) = some .voAndPrepositions := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch95 :
    (Core.WALS.F95A.lookup "jpn").map (·.value) = some .ovAndPostpositions := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch95 :
    (Core.WALS.F95A.lookup "tur").map (·.value) = some .ovAndPostpositions := by decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_ch95 :
    (Core.WALS.F95A.lookup "hin").map (·.value) = some .ovAndPostpositions := by decide

set_option maxRecDepth 4096 in
theorem korean_ch95 :
    (Core.WALS.F95A.lookup "kor").map (·.value) = some .ovAndPostpositions := by decide

set_option maxRecDepth 4096 in
theorem basque_ch95 :
    (Core.WALS.F95A.lookup "bsq").map (·.value) = some .ovAndPostpositions := by decide

set_option maxRecDepth 4096 in
-- Mandarin is "other" in Ch 95A (SVO but mixed adpositions)
theorem mandarin_ch95 :
    (Core.WALS.F95A.lookup "mnd").map (·.value) = some .other := by decide

set_option maxRecDepth 4096 in
theorem russian_ch95 :
    (Core.WALS.F95A.lookup "rus").map (·.value) = some .voAndPrepositions := by decide

set_option maxRecDepth 4096 in
theorem swahili_ch95 :
    (Core.WALS.F95A.lookup "swa").map (·.value) = some .voAndPrepositions := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch95 :
    (Core.WALS.F95A.lookup "ind").map (·.value) = some .voAndPrepositions := by decide

set_option maxRecDepth 4096 in
theorem arabic_ch95 :
    (Core.WALS.F95A.lookup "ams").map (·.value) = some .voAndPrepositions := by decide

set_option maxRecDepth 4096 in
theorem irish_ch95 :
    (Core.WALS.F95A.lookup "iri").map (·.value) = some .voAndPrepositions := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch95 :
    (Core.WALS.F95A.lookup "mal").map (·.value) = some .voAndPrepositions := by decide

set_option maxRecDepth 4096 in
theorem tzotzil_ch95 :
    (Core.WALS.F95A.lookup "tzo").map (·.value) = some .voAndPrepositions := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch95 :
    (Core.WALS.F95A.lookup "hix").map (·.value) = some .ovAndPostpositions := by decide

set_option maxRecDepth 4096 in
-- German is "other" in Ch 95A (mixed OV/VO with prepositions)
theorem german_ch95 :
    (Core.WALS.F95A.lookup "ger").map (·.value) = some .other := by decide

set_option maxRecDepth 4096 in
-- Warlpiri is "other" in Ch 95A (no dominant OV order)
theorem warlpiri_ch95 :
    (Core.WALS.F95A.lookup "wrl").map (·.value) = some .other := by decide

set_option maxRecDepth 4096 in
theorem welsh_ch95 :
    (Core.WALS.F95A.lookup "wel").map (·.value) = some .voAndPrepositions := by decide

-- ============================================================================
-- Chapter 96: Relationship between Order of OV and Relative Clause-Noun
-- ============================================================================

-- WALS Ch 96: Cross-tabulation of O-V order with relative clause order.
-- Another harmonic pair test: OV+RelN vs VO+NRel.

/-- Ch 96 total: 879 languages. -/
theorem ch96_total : ch96.length = 879 :=
  Core.WALS.F96A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 96
theorem ch96_count_ovAndReln :
    (ch96.filter (·.value == .ovAndReln)).length = 132 := by decide

set_option maxRecDepth 4096 in
theorem ch96_count_ovAndNrel :
    (ch96.filter (·.value == .ovAndNrel)).length = 113 := by decide

set_option maxRecDepth 4096 in
theorem ch96_count_voAndReln :
    (ch96.filter (·.value == .voAndReln)).length = 5 := by decide

set_option maxRecDepth 4096 in
theorem ch96_count_voAndNrel :
    (ch96.filter (·.value == .voAndNrel)).length = 416 := by decide

set_option maxRecDepth 4096 in
theorem ch96_count_other :
    (ch96.filter (·.value == .other)).length = 213 := by decide

set_option maxRecDepth 8192 in
-- VO+NRel strongly dominates VO+RelN (relative clauses are recursive, so head
-- direction matters). OV languages are more mixed due to the N-RelCl strategy.
theorem ch96_voNRel_dominant :
    (ch96.filter (·.value == .voAndNrel)).length >
    (ch96.filter (·.value == .voAndReln)).length * 80 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 96A
-- Note: Arabic (MSA), Tzotzil are absent from Ch 96A.
theorem english_ch96 :
    (Core.WALS.F96A.lookup "eng").map (·.value) = some .voAndNrel := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch96 :
    (Core.WALS.F96A.lookup "jpn").map (·.value) = some .ovAndReln := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch96 :
    (Core.WALS.F96A.lookup "tur").map (·.value) = some .ovAndReln := by decide

set_option maxRecDepth 4096 in
-- Hindi is "other" in Ch 96A (correlative relative clauses are neither pre- nor postnominal)
theorem hindiUrdu_ch96 :
    (Core.WALS.F96A.lookup "hin").map (·.value) = some .other := by decide

set_option maxRecDepth 4096 in
theorem korean_ch96 :
    (Core.WALS.F96A.lookup "kor").map (·.value) = some .ovAndReln := by decide

set_option maxRecDepth 4096 in
theorem basque_ch96 :
    (Core.WALS.F96A.lookup "bsq").map (·.value) = some .ovAndReln := by decide

set_option maxRecDepth 4096 in
-- Mandarin is VO+RelN (disharmonic: SVO with prenominal relative clauses)
theorem mandarin_ch96 :
    (Core.WALS.F96A.lookup "mnd").map (·.value) = some .voAndReln := by decide

set_option maxRecDepth 4096 in
theorem russian_ch96 :
    (Core.WALS.F96A.lookup "rus").map (·.value) = some .voAndNrel := by decide

set_option maxRecDepth 4096 in
theorem swahili_ch96 :
    (Core.WALS.F96A.lookup "swa").map (·.value) = some .voAndNrel := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch96 :
    (Core.WALS.F96A.lookup "ind").map (·.value) = some .voAndNrel := by decide

set_option maxRecDepth 4096 in
theorem irish_ch96 :
    (Core.WALS.F96A.lookup "iri").map (·.value) = some .voAndNrel := by decide

set_option maxRecDepth 4096 in
theorem tagalog_ch96 :
    (Core.WALS.F96A.lookup "tag").map (·.value) = some .voAndNrel := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch96 :
    (Core.WALS.F96A.lookup "mal").map (·.value) = some .voAndNrel := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch96 :
    (Core.WALS.F96A.lookup "hix").map (·.value) = some .ovAndNrel := by decide

set_option maxRecDepth 4096 in
-- German is "other" in Ch 96A (mixed OV/VO status)
theorem german_ch96 :
    (Core.WALS.F96A.lookup "ger").map (·.value) = some .other := by decide

set_option maxRecDepth 4096 in
-- Warlpiri is "other" in Ch 96A (adjoined relative clauses, no dominant OV)
theorem warlpiri_ch96 :
    (Core.WALS.F96A.lookup "wrl").map (·.value) = some .other := by decide

set_option maxRecDepth 4096 in
theorem welsh_ch96 :
    (Core.WALS.F96A.lookup "wel").map (·.value) = some .voAndNrel := by decide

-- ============================================================================
-- Chapter 97: Relationship between Order of OV and Adjective-Noun
-- ============================================================================

-- WALS Ch 97: Cross-tabulation of O-V order with adjective-noun order.
-- Unlike Ch 95 and 96, this pairing shows weaker correlation because
-- adjectives are typically single words (a single-word exception).

/-- Ch 97 total: 1316 languages. -/
theorem ch97_total : ch97.length = 1316 :=
  Core.WALS.F97A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 97
theorem ch97_count_ovAndAdjn :
    (ch97.filter (·.value == .ovAndAdjn)).length = 216 := by decide

set_option maxRecDepth 4096 in
theorem ch97_count_ovAndNadj :
    (ch97.filter (·.value == .ovAndNadj)).length = 332 := by decide

set_option maxRecDepth 4096 in
theorem ch97_count_voAndAdjn :
    (ch97.filter (·.value == .voAndAdjn)).length = 114 := by decide

set_option maxRecDepth 4096 in
theorem ch97_count_voAndNadj :
    (ch97.filter (·.value == .voAndNadj)).length = 456 := by decide

set_option maxRecDepth 4096 in
theorem ch97_count_other :
    (ch97.filter (·.value == .other)).length = 198 := by decide

set_option maxRecDepth 8192 in
-- OV languages split between AdjN and NAdj (weak correlation, single-word exception).
-- This contrasts with Ch 95 where OV+Prep is nearly absent.
theorem ch97_ov_split :
    let ovAdjN := (ch97.filter (·.value == .ovAndAdjn)).length
    let ovNAdj := (ch97.filter (·.value == .ovAndNadj)).length
    ovNAdj > ovAdjN := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 97A
theorem english_ch97 :
    (Core.WALS.F97A.lookup "eng").map (·.value) = some .voAndAdjn := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch97 :
    (Core.WALS.F97A.lookup "jpn").map (·.value) = some .ovAndAdjn := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch97 :
    (Core.WALS.F97A.lookup "tur").map (·.value) = some .ovAndAdjn := by decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_ch97 :
    (Core.WALS.F97A.lookup "hin").map (·.value) = some .ovAndAdjn := by decide

set_option maxRecDepth 4096 in
theorem korean_ch97 :
    (Core.WALS.F97A.lookup "kor").map (·.value) = some .ovAndAdjn := by decide

set_option maxRecDepth 4096 in
-- Basque is OV+NAdj (disharmonic for Adj-N, consistent with single-word exception)
theorem basque_ch97 :
    (Core.WALS.F97A.lookup "bsq").map (·.value) = some .ovAndNadj := by decide

set_option maxRecDepth 4096 in
-- Mandarin is VO+AdjN (disharmonic: SVO with prenominal adjectives)
theorem mandarin_ch97 :
    (Core.WALS.F97A.lookup "mnd").map (·.value) = some .voAndAdjn := by decide

set_option maxRecDepth 4096 in
theorem russian_ch97 :
    (Core.WALS.F97A.lookup "rus").map (·.value) = some .voAndAdjn := by decide

set_option maxRecDepth 4096 in
theorem swahili_ch97 :
    (Core.WALS.F97A.lookup "swa").map (·.value) = some .voAndNadj := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch97 :
    (Core.WALS.F97A.lookup "ind").map (·.value) = some .voAndNadj := by decide

set_option maxRecDepth 4096 in
theorem arabic_ch97 :
    (Core.WALS.F97A.lookup "ams").map (·.value) = some .voAndNadj := by decide

set_option maxRecDepth 4096 in
theorem irish_ch97 :
    (Core.WALS.F97A.lookup "iri").map (·.value) = some .voAndNadj := by decide

set_option maxRecDepth 4096 in
-- Tagalog is "other" in Ch 97A (no dominant Adj-N order)
theorem tagalog_ch97 :
    (Core.WALS.F97A.lookup "tag").map (·.value) = some .other := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch97 :
    (Core.WALS.F97A.lookup "mal").map (·.value) = some .voAndNadj := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch97 :
    (Core.WALS.F97A.lookup "hix").map (·.value) = some .ovAndNadj := by decide

set_option maxRecDepth 4096 in
-- German is "other" in Ch 97A (mixed OV/VO)
theorem german_ch97 :
    (Core.WALS.F97A.lookup "ger").map (·.value) = some .other := by decide

set_option maxRecDepth 4096 in
-- Warlpiri is "other" in Ch 97A (no dominant OV order)
theorem warlpiri_ch97 :
    (Core.WALS.F97A.lookup "wrl").map (·.value) = some .other := by decide

set_option maxRecDepth 4096 in
theorem welsh_ch97 :
    (Core.WALS.F97A.lookup "wel").map (·.value) = some .voAndNadj := by decide

-- ============================================================================
-- Chapter 81B: Languages with two Dominant Orders of Subject, Object, and Verb
-- ============================================================================

-- WALS Ch 81B catalogs languages where two basic word orders co-occur as
-- dominant patterns. SOV-or-SVO is the most common dual-order combination,
-- consistent with the general dominance of subject-first orders.

/-- Ch 81B total: 67 languages. -/
theorem ch81B_total : ch81B.length = 67 :=
  Core.WALS.F81B.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 81B
theorem ch81B_count_sovOrSvo :
    (ch81B.filter (·.value == .sovOrSvo)).length = 29 := by decide

set_option maxRecDepth 4096 in
theorem ch81B_count_vsoOrVos :
    (ch81B.filter (·.value == .vsoOrVos)).length = 14 := by decide

set_option maxRecDepth 4096 in
theorem ch81B_count_svoOrVso :
    (ch81B.filter (·.value == .svoOrVso)).length = 13 := by decide

set_option maxRecDepth 4096 in
theorem ch81B_count_svoOrVos :
    (ch81B.filter (·.value == .svoOrVos)).length = 8 := by decide

set_option maxRecDepth 4096 in
theorem ch81B_count_sovOrOvs :
    (ch81B.filter (·.value == .sovOrOvs)).length = 3 := by decide

set_option maxRecDepth 8192 in
-- SOV-or-SVO is the most common dual-order pattern
theorem ch81B_sovOrSvo_most_common :
    (ch81B.filter (·.value == .sovOrSvo)).length >
    (ch81B.filter (·.value == .vsoOrVos)).length := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 81B
-- Hungarian, German are in our profile set and appear in Ch 81B.
-- (German is classified as SOV-or-SVO in Ch 81B, consistent with V2 analysis.)
theorem german_ch81B :
    (Core.WALS.F81B.lookup "ger").map (·.value) = some .sovOrSvo := by decide

set_option maxRecDepth 4096 in
theorem hungarian_ch81B :
    (Core.WALS.F81B.lookup "hun").map (·.value) = some .sovOrSvo := by decide

-- ============================================================================
-- Chapter 90B: Prenominal relative clauses
-- ============================================================================

-- WALS Ch 90B sub-feature: classifies languages that have prenominal (RelN)
-- relative clauses, distinguishing dominant RelN from mixed strategies.

/-- Ch 90B total: 191 languages. -/
theorem ch90B_total : ch90B.length = 191 :=
  Core.WALS.F90B.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 90B
theorem ch90B_count_relativeClauseNounDominant :
    (ch90B.filter (·.value == .relativeClauseNounDominant)).length = 141 := by decide

set_option maxRecDepth 4096 in
theorem ch90B_count_relnOrNrel :
    (ch90B.filter (·.value == .relnOrNrel)).length = 29 := by decide

set_option maxRecDepth 4096 in
theorem ch90B_count_relnOrInternallyHeaded :
    (ch90B.filter (·.value == .relnOrInternallyHeaded)).length = 15 := by decide

set_option maxRecDepth 4096 in
theorem ch90B_count_relnOrCorrelative :
    (ch90B.filter (·.value == .relnOrCorrelative)).length = 5 := by decide

set_option maxRecDepth 4096 in
theorem ch90B_count_relnOrDoubleHeaded :
    (ch90B.filter (·.value == .relnOrDoubleHeaded)).length = 1 := by decide

set_option maxRecDepth 4096 in
-- Dominant-only prenominal (RelN) is the majority among languages with this strategy
theorem ch90B_dominant_relN_majority :
    (ch90B.filter (·.value == .relativeClauseNounDominant)).length >
    ch90B.length / 2 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 90B
-- Japanese, Korean, Turkish, Mandarin, Basque all have dominant prenominal RelCl.
-- Hungarian has RelN-or-NRel (mixed).
theorem japanese_ch90B :
    (Core.WALS.F90B.lookup "jpn").map (·.value) =
    some .relativeClauseNounDominant := by decide

set_option maxRecDepth 4096 in
theorem korean_ch90B :
    (Core.WALS.F90B.lookup "kor").map (·.value) =
    some .relativeClauseNounDominant := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch90B :
    (Core.WALS.F90B.lookup "tur").map (·.value) =
    some .relativeClauseNounDominant := by decide

set_option maxRecDepth 4096 in
theorem mandarin_ch90B :
    (Core.WALS.F90B.lookup "mnd").map (·.value) =
    some .relativeClauseNounDominant := by decide

set_option maxRecDepth 4096 in
theorem basque_ch90B :
    (Core.WALS.F90B.lookup "bsq").map (·.value) =
    some .relativeClauseNounDominant := by decide

set_option maxRecDepth 4096 in
theorem hungarian_ch90B :
    (Core.WALS.F90B.lookup "hun").map (·.value) =
    some .relnOrNrel := by decide

-- ============================================================================
-- Chapter 90C: Postnominal relative clauses
-- ============================================================================

-- WALS Ch 90C sub-feature: classifies languages that have postnominal (NRel)
-- relative clauses. This is the largest Ch 90 sub-feature (620 languages),
-- reflecting the cross-linguistic dominance of postnominal relative clauses.

/-- Ch 90C total: 620 languages. -/
theorem ch90C_total : ch90C.length = 620 :=
  Core.WALS.F90C.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 90C
theorem ch90C_count_nounRelativeClauseDominant :
    (ch90C.filter (·.value == .nounRelativeClauseDominant)).length = 579 := by decide

set_option maxRecDepth 4096 in
theorem ch90C_count_nrelOrReln :
    (ch90C.filter (·.value == .nrelOrReln)).length = 31 := by decide

set_option maxRecDepth 4096 in
theorem ch90C_count_nrelOrInternallyHeaded :
    (ch90C.filter (·.value == .nrelOrInternallyHeaded)).length = 8 := by decide

set_option maxRecDepth 4096 in
theorem ch90C_count_nrelOrCorrelative :
    (ch90C.filter (·.value == .nrelOrCorrelative)).length = 2 := by decide

set_option maxRecDepth 4096 in
-- Dominant-only postnominal (NRel) is overwhelmingly the majority
theorem ch90C_dominant_nRel_majority :
    (ch90C.filter (·.value == .nounRelativeClauseDominant)).length >
    ch90C.length * 9 / 10 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 90C
-- English, Russian, Swahili, Indonesian, Irish, Welsh, German, Hixkaryana,
-- Tagalog, Malagasy all have dominant postnominal RelCl.
-- Hungarian has NRel-or-RelN (mixed).
theorem english_ch90C :
    (Core.WALS.F90C.lookup "eng").map (·.value) =
    some .nounRelativeClauseDominant := by decide

set_option maxRecDepth 4096 in
theorem russian_ch90C :
    (Core.WALS.F90C.lookup "rus").map (·.value) =
    some .nounRelativeClauseDominant := by decide

set_option maxRecDepth 4096 in
theorem swahili_ch90C :
    (Core.WALS.F90C.lookup "swa").map (·.value) =
    some .nounRelativeClauseDominant := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch90C :
    (Core.WALS.F90C.lookup "ind").map (·.value) =
    some .nounRelativeClauseDominant := by decide

set_option maxRecDepth 4096 in
theorem irish_ch90C :
    (Core.WALS.F90C.lookup "iri").map (·.value) =
    some .nounRelativeClauseDominant := by decide

set_option maxRecDepth 4096 in
theorem welsh_ch90C :
    (Core.WALS.F90C.lookup "wel").map (·.value) =
    some .nounRelativeClauseDominant := by decide

set_option maxRecDepth 4096 in
theorem german_ch90C :
    (Core.WALS.F90C.lookup "ger").map (·.value) =
    some .nounRelativeClauseDominant := by decide

set_option maxRecDepth 4096 in
theorem hixkaryana_ch90C :
    (Core.WALS.F90C.lookup "hix").map (·.value) =
    some .nounRelativeClauseDominant := by decide

set_option maxRecDepth 4096 in
theorem tagalog_ch90C :
    (Core.WALS.F90C.lookup "tag").map (·.value) =
    some .nounRelativeClauseDominant := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch90C :
    (Core.WALS.F90C.lookup "mal").map (·.value) =
    some .nounRelativeClauseDominant := by decide

set_option maxRecDepth 4096 in
theorem hungarian_ch90C :
    (Core.WALS.F90C.lookup "hun").map (·.value) =
    some .nrelOrReln := by decide

-- ============================================================================
-- Chapter 90D: Internally-headed relative clauses
-- ============================================================================

-- WALS Ch 90D sub-feature: classifies languages that have internally-headed
-- relative clauses. Japanese and Korean have this strategy as a nondominant type.

/-- Ch 90D total: 63 languages. -/
theorem ch90D_total : ch90D.length = 63 :=
  Core.WALS.F90D.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 90D
theorem ch90D_count_internallyHeadedRelativeClauseDominant :
    (ch90D.filter (·.value == .internallyHeadedRelativeClauseDominant)).length = 24 := by decide

set_option maxRecDepth 4096 in
theorem ch90D_count_internallyHeadedOrReln :
    (ch90D.filter (·.value == .internallyHeadedOrReln)).length = 15 := by decide

set_option maxRecDepth 4096 in
theorem ch90D_count_internallyHeadedOrNrel :
    (ch90D.filter (·.value == .internallyHeadedOrNrel)).length = 8 := by decide

set_option maxRecDepth 4096 in
theorem ch90D_count_internallyHeadedOrCorrelative :
    (ch90D.filter (·.value == .internallyHeadedOrCorrelative)).length = 1 := by decide

set_option maxRecDepth 4096 in
theorem ch90D_count_internallyHeadedOrDoubleHeaded :
    (ch90D.filter (·.value == .internallyHeadedOrDoubleHeaded)).length = 1 := by decide

set_option maxRecDepth 4096 in
theorem ch90D_count_internallyHeadedOccursAsNondominantType :
    (ch90D.filter (·.value == .internallyHeadedOccursAsNondominantType)).length = 10 := by decide

set_option maxRecDepth 4096 in
theorem ch90D_count_internallyHeadedExists :
    (ch90D.filter (·.value == .internallyHeadedExists)).length = 4 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 90D
-- Japanese and Korean have internally-headed as a nondominant type.
-- Tagalog also has internally-headed as a nondominant type.
theorem japanese_ch90D :
    (Core.WALS.F90D.lookup "jpn").map (·.value) =
    some .internallyHeadedOccursAsNondominantType := by decide

set_option maxRecDepth 4096 in
theorem korean_ch90D :
    (Core.WALS.F90D.lookup "kor").map (·.value) =
    some .internallyHeadedOccursAsNondominantType := by decide

set_option maxRecDepth 4096 in
theorem tagalog_ch90D :
    (Core.WALS.F90D.lookup "tag").map (·.value) =
    some .internallyHeadedOccursAsNondominantType := by decide

-- ============================================================================
-- Chapter 90E: Correlative relative clauses
-- ============================================================================

-- WALS Ch 90E sub-feature: classifies languages that have correlative relative
-- clauses. Hindi is the canonical example with dominant correlative strategy.

/-- Ch 90E total: 23 languages. -/
theorem ch90E_total : ch90E.length = 23 :=
  Core.WALS.F90E.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 90E
theorem ch90E_count_correlativeRelativeClauseDominant :
    (ch90E.filter (·.value == .correlativeRelativeClauseDominant)).length = 7 := by decide

set_option maxRecDepth 4096 in
theorem ch90E_count_correlativeOrReln :
    (ch90E.filter (·.value == .correlativeOrReln)).length = 7 := by decide

set_option maxRecDepth 4096 in
theorem ch90E_count_correlativeOrNrel :
    (ch90E.filter (·.value == .correlativeOrNrel)).length = 2 := by decide

set_option maxRecDepth 4096 in
theorem ch90E_count_correlativeOrInternallyHeaded :
    (ch90E.filter (·.value == .correlativeOrInternallyHeaded)).length = 1 := by decide

set_option maxRecDepth 4096 in
theorem ch90E_count_correlativeOrAdjoined :
    (ch90E.filter (·.value == .correlativeOrAdjoined)).length = 2 := by decide

set_option maxRecDepth 4096 in
theorem ch90E_count_correlativeAsNondominantType :
    (ch90E.filter (·.value == .correlativeAsNondominantType)).length = 3 := by decide

set_option maxRecDepth 4096 in
theorem ch90E_count_correlativeExists :
    (ch90E.filter (·.value == .correlativeExists)).length = 1 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 90E
-- Hindi has dominant correlative relative clauses (consistent with Ch 90A coding).
theorem hindiUrdu_ch90E :
    (Core.WALS.F90E.lookup "hin").map (·.value) =
    some .correlativeRelativeClauseDominant := by decide

-- ============================================================================
-- Chapter 90F: Adjoined relative clauses
-- ============================================================================

-- WALS Ch 90F sub-feature: classifies languages that have adjoined relative
-- clauses. Warlpiri is the canonical example (dominant adjoined strategy).

/-- Ch 90F total: 10 languages. -/
theorem ch90F_total : ch90F.length = 10 :=
  Core.WALS.F90F.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 90F
theorem ch90F_count_adjoinedRelativeClauseDominant :
    (ch90F.filter (·.value == .adjoinedRelativeClauseDominant)).length = 8 := by decide

set_option maxRecDepth 4096 in
theorem ch90F_count_adjoinedOrCorrelative :
    (ch90F.filter (·.value == .adjoinedOrCorrelative)).length = 2 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 90F
-- Warlpiri has dominant adjoined relative clauses (consistent with Ch 90A coding).
theorem warlpiri_ch90F :
    (Core.WALS.F90F.lookup "wrl").map (·.value) =
    some .adjoinedRelativeClauseDominant := by decide

-- ============================================================================
-- Chapter 90G: Double-headed relative clauses
-- ============================================================================

-- WALS Ch 90G sub-feature: classifies languages that have double-headed
-- relative clauses. Only 5 languages in the sample; none overlap with our profiles.

/-- Ch 90G total: 5 languages. -/
theorem ch90G_total : ch90G.length = 5 :=
  Core.WALS.F90G.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 90G
theorem ch90G_count_doubleHeadedDominant :
    (ch90G.filter (·.value == .doubleHeadedDominant)).length = 1 := by decide

set_option maxRecDepth 4096 in
theorem ch90G_count_doubleHeadedOrReln :
    (ch90G.filter (·.value == .doubleHeadedOrReln)).length = 1 := by decide

set_option maxRecDepth 4096 in
theorem ch90G_count_doubleHeadedOrInternallyHeaded :
    (ch90G.filter (·.value == .doubleHeadedOrInternallyHeaded)).length = 1 := by decide

set_option maxRecDepth 4096 in
theorem ch90G_count_doubleHeadedAsNondominantType :
    (ch90G.filter (·.value == .doubleHeadedAsNondominantType)).length = 2 := by decide

-- ============================================================================
-- Chapter 60: Genitives, Adjectives and Relative Clauses
-- ============================================================================

-- WALS Ch 60A classifies the degree of formal differentiation between
-- genitives, adjectives, and relative clauses within a language. "Highly
-- differentiated" means the three categories have clearly distinct syntax;
-- "weakly differentiated" means they overlap significantly.

/-- Ch 60 total: 138 languages. -/
theorem ch60_total : ch60.length = 138 :=
  Core.WALS.F60A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 60
theorem ch60_count_weaklyDifferentiated :
    (ch60.filter (·.value == .weaklyDifferentiated)).length = 15 := by decide

set_option maxRecDepth 4096 in
theorem ch60_count_genitivesAndAdjectivesCollapsed :
    (ch60.filter (·.value == .genitivesAndAdjectivesCollapsed)).length = 8 := by decide

set_option maxRecDepth 4096 in
theorem ch60_count_genitivesAndRelativeClausesCollapsed :
    (ch60.filter (·.value == .genitivesAndRelativeClausesCollapsed)).length = 2 := by decide

set_option maxRecDepth 4096 in
theorem ch60_count_adjectivesAndRelativeClausesCollapsed :
    (ch60.filter (·.value == .adjectivesAndRelativeClausesCollapsed)).length = 33 := by decide

set_option maxRecDepth 4096 in
theorem ch60_count_moderatelyDifferentiatedInOtherWays :
    (ch60.filter (·.value == .moderatelyDifferentiatedInOtherWays)).length = 3 := by decide

set_option maxRecDepth 4096 in
theorem ch60_count_highlyDifferentiated :
    (ch60.filter (·.value == .highlyDifferentiated)).length = 77 := by decide

set_option maxRecDepth 4096 in
-- "Highly differentiated" is the majority value
theorem ch60_highlyDifferentiated_majority :
    (ch60.filter (·.value == .highlyDifferentiated)).length >
    ch60.length / 2 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 60A
-- English, Hindi, Basque, Korean, Russian, Turkish, Hungarian are highly differentiated.
-- Japanese has genitives and adjectives collapsed.
-- Mandarin, Indonesian are weakly differentiated.
-- Tagalog, Malagasy have adjectives and relative clauses collapsed.
theorem english_ch60 :
    (Core.WALS.F60A.lookup "eng").map (·.value) =
    some .highlyDifferentiated := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch60 :
    (Core.WALS.F60A.lookup "jpn").map (·.value) =
    some .genitivesAndAdjectivesCollapsed := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch60 :
    (Core.WALS.F60A.lookup "tur").map (·.value) =
    some .highlyDifferentiated := by decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_ch60 :
    (Core.WALS.F60A.lookup "hin").map (·.value) =
    some .highlyDifferentiated := by decide

set_option maxRecDepth 4096 in
theorem korean_ch60 :
    (Core.WALS.F60A.lookup "kor").map (·.value) =
    some .highlyDifferentiated := by decide

set_option maxRecDepth 4096 in
theorem basque_ch60 :
    (Core.WALS.F60A.lookup "bsq").map (·.value) =
    some .highlyDifferentiated := by decide

set_option maxRecDepth 4096 in
theorem mandarin_ch60 :
    (Core.WALS.F60A.lookup "mnd").map (·.value) =
    some .weaklyDifferentiated := by decide

set_option maxRecDepth 4096 in
theorem russian_ch60 :
    (Core.WALS.F60A.lookup "rus").map (·.value) =
    some .highlyDifferentiated := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch60 :
    (Core.WALS.F60A.lookup "ind").map (·.value) =
    some .weaklyDifferentiated := by decide

set_option maxRecDepth 4096 in
theorem tagalog_ch60 :
    (Core.WALS.F60A.lookup "tag").map (·.value) =
    some .adjectivesAndRelativeClausesCollapsed := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch60 :
    (Core.WALS.F60A.lookup "mal").map (·.value) =
    some .adjectivesAndRelativeClausesCollapsed := by decide

set_option maxRecDepth 4096 in
theorem hungarian_ch60 :
    (Core.WALS.F60A.lookup "hun").map (·.value) =
    some .highlyDifferentiated := by decide

-- ============================================================================
-- Chapter 61: Adjectives without Nouns
-- ============================================================================

-- WALS Ch 61A classifies how a language forms headless adjective phrases
-- (e.g., "the tall one" in English). Some languages use bare adjectives,
-- others require overt morphological or syntactic marking.

/-- Ch 61 total: 124 languages. -/
theorem ch61_total : ch61.length = 124 :=
  Core.WALS.F61A.total_count

set_option maxRecDepth 4096 in
-- Distribution counts for Ch 61
theorem ch61_count_notWithoutNoun :
    (ch61.filter (·.value == .notWithoutNoun)).length = 1 := by decide

set_option maxRecDepth 4096 in
theorem ch61_count_withoutMarking :
    (ch61.filter (·.value == .withoutMarking)).length = 73 := by decide

set_option maxRecDepth 4096 in
theorem ch61_count_markedByPrefix :
    (ch61.filter (·.value == .markedByPrefix)).length = 7 := by decide

set_option maxRecDepth 4096 in
theorem ch61_count_markedBySuffix :
    (ch61.filter (·.value == .markedBySuffix)).length = 13 := by decide

set_option maxRecDepth 4096 in
theorem ch61_count_markedByPrecedingWord :
    (ch61.filter (·.value == .markedByPrecedingWord)).length = 18 := by decide

set_option maxRecDepth 4096 in
theorem ch61_count_markedByFollowingWord :
    (ch61.filter (·.value == .markedByFollowingWord)).length = 7 := by decide

set_option maxRecDepth 4096 in
theorem ch61_count_markedByMixedOrOtherStrategies :
    (ch61.filter (·.value == .markedByMixedOrOtherStrategies)).length = 5 := by decide

set_option maxRecDepth 4096 in
-- "Without marking" is the majority strategy for headless adjective phrases
theorem ch61_withoutMarking_majority :
    (ch61.filter (·.value == .withoutMarking)).length >
    ch61.length / 2 := by decide

set_option maxRecDepth 4096 in
-- Per-language grounding: Ch 61A
-- English, Hindi, Korean, Mandarin use "marked by following word" (e.g., "one").
-- Japanese uses "mixed or other strategies".
-- Turkish, Basque, Russian, Swahili, Tagalog, Hungarian use "without marking".
-- Indonesian, Irish, Malagasy use "marked by preceding word".
theorem english_ch61 :
    (Core.WALS.F61A.lookup "eng").map (·.value) =
    some .markedByFollowingWord := by decide

set_option maxRecDepth 4096 in
theorem japanese_ch61 :
    (Core.WALS.F61A.lookup "jpn").map (·.value) =
    some .markedByMixedOrOtherStrategies := by decide

set_option maxRecDepth 4096 in
theorem turkish_ch61 :
    (Core.WALS.F61A.lookup "tur").map (·.value) =
    some .withoutMarking := by decide

set_option maxRecDepth 4096 in
theorem hindiUrdu_ch61 :
    (Core.WALS.F61A.lookup "hin").map (·.value) =
    some .markedByFollowingWord := by decide

set_option maxRecDepth 4096 in
theorem korean_ch61 :
    (Core.WALS.F61A.lookup "kor").map (·.value) =
    some .markedByFollowingWord := by decide

set_option maxRecDepth 4096 in
theorem basque_ch61 :
    (Core.WALS.F61A.lookup "bsq").map (·.value) =
    some .withoutMarking := by decide

set_option maxRecDepth 4096 in
theorem mandarin_ch61 :
    (Core.WALS.F61A.lookup "mnd").map (·.value) =
    some .markedByFollowingWord := by decide

set_option maxRecDepth 4096 in
theorem russian_ch61 :
    (Core.WALS.F61A.lookup "rus").map (·.value) =
    some .withoutMarking := by decide

set_option maxRecDepth 4096 in
theorem swahili_ch61 :
    (Core.WALS.F61A.lookup "swa").map (·.value) =
    some .withoutMarking := by decide

set_option maxRecDepth 4096 in
theorem indonesian_ch61 :
    (Core.WALS.F61A.lookup "ind").map (·.value) =
    some .markedByPrecedingWord := by decide

set_option maxRecDepth 4096 in
theorem irish_ch61 :
    (Core.WALS.F61A.lookup "iri").map (·.value) =
    some .markedByPrecedingWord := by decide

set_option maxRecDepth 4096 in
theorem tagalog_ch61 :
    (Core.WALS.F61A.lookup "tag").map (·.value) =
    some .withoutMarking := by decide

set_option maxRecDepth 4096 in
theorem malagasy_ch61 :
    (Core.WALS.F61A.lookup "mal").map (·.value) =
    some .markedByPrecedingWord := by decide

set_option maxRecDepth 4096 in
theorem hungarian_ch61 :
    (Core.WALS.F61A.lookup "hun").map (·.value) =
    some .withoutMarking := by decide

end Phenomena.WordOrder.Typology
