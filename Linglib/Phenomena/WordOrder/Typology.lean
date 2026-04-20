import Linglib.Core.Lexical.Word
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

## Per-language and per-chapter data lookups

This file keeps language-profile records (`english`, `japanese`, ...) and the
cross-linguistic *generalizations* derived from WALS. Per-language WALS-
agreement theorems (`english_ch85`, `japanese_order_wals`, ...) and per-cell
distribution counts (`ch85_count_postpositions`, ...) have been removed: in
the long-term architecture, language profiles are functions of WALS lookups,
so per-language agreement is true by construction. Distribution counts can be
recovered directly from `Core.WALS.Features.F*` if needed.

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

    The order fields (`basicOrder`, `svOrder`, `ovOrder`) are derived from
    `Core.WALS` via ISO 639-3 lookup — they are not hand-coded. Cross-chapter
    consistency theorems (e.g., `sov_implies_sv_and_ov`) thus test WALS's
    internal consistency rather than the agreement of hand-coded fields. -/
structure BasicOrderProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Notes on the word-order system. -/
  notes : String := ""
  deriving Repr

/-- Convert WALS F81A's BasicWordOrder to our local BasicOrder. -/
private def fromWALS81A : Core.WALS.F81A.BasicWordOrder → BasicOrder
  | .sov => .sov
  | .svo => .svo
  | .vso => .vso
  | .vos => .vos
  | .ovs => .ovs
  | .osv => .osv
  | .noDominantOrder => .noDominant

/-- Convert WALS F82A's SubjectVerbOrder to our local SVOrder. -/
private def fromWALS82A : Core.WALS.F82A.SubjectVerbOrder → SVOrder
  | .sv => .sv
  | .vs => .vs
  | .noDominantOrder => .noDominant

/-- Convert WALS F83A's ObjectVerbOrder to our local OVOrder. -/
private def fromWALS83A : Core.WALS.F83A.ObjectVerbOrder → OVOrder
  | .ov => .ov
  | .vo => .vo
  | .noDominantOrder => .noDominant

/-- Ch 81 basic order, derived from WALS by ISO lookup.
    Returns `.noDominant` for languages absent from WALS F81A. -/
def BasicOrderProfile.basicOrder (p : BasicOrderProfile) : BasicOrder :=
  match Core.WALS.Datapoint.lookupISO Core.WALS.F81A.allData p.iso with
  | some d => fromWALS81A d.value
  | none => .noDominant

/-- Ch 82 subject-verb order, derived from WALS by ISO lookup.
    Returns `.noDominant` for languages absent from WALS F82A. -/
def BasicOrderProfile.svOrder (p : BasicOrderProfile) : SVOrder :=
  match Core.WALS.Datapoint.lookupISO Core.WALS.F82A.allData p.iso with
  | some d => fromWALS82A d.value
  | none => .noDominant

/-- Ch 83 object-verb order, derived from WALS by ISO lookup.
    Returns `.noDominant` for languages absent from WALS F83A. -/
def BasicOrderProfile.ovOrder (p : BasicOrderProfile) : OVOrder :=
  match Core.WALS.Datapoint.lookupISO Core.WALS.F83A.allData p.iso with
  | some d => fromWALS83A d.value
  | none => .noDominant

-- ---- SOV languages ----

/-- Japanese: rigid SOV with postpositions, relative clause before noun,
    genitive before noun. The canonical head-final language. -/
def japanese : BasicOrderProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , notes := "Rigid SOV; canonical head-final" }

/-- Turkish: SOV with postpositions. Relatively free word order for
    pragmatic effects, but SOV is strongly dominant. -/
def turkish : BasicOrderProfile :=
  { language := "Turkish"
  , iso := "tur"
  , notes := "SOV dominant; some pragmatic reordering" }

/-- Hindi-Urdu: SOV with postpositions. Word order is relatively flexible
    due to case marking, but SOV is the default neutral order. -/
def hindiUrdu : BasicOrderProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , notes := "SOV default; case marking allows scrambling" }

/-- Korean: rigid SOV with postpositions, relative clause before noun.
    Very similar head-final profile to Japanese. -/
def korean : BasicOrderProfile :=
  { language := "Korean"
  , iso := "kor"
  , notes := "Rigid SOV; head-final like Japanese" }

/-- Quechua (Southern): rigid SOV with postpositions, suffixal morphology.
    One of the most consistently head-final languages. -/
def quechua : BasicOrderProfile :=
  { language := "Quechua"
  , iso := "que"
  , notes := "Rigid SOV; consistently head-final. NOTE: absent from WALS F81A/F82A/F83A; derived order accessors return .noDominant. Reference grammars (e.g., Weber 1989) classify Huallaga Quechua as SOV with postpositions." }

/-- Basque: SOV with postpositions. Ergative-absolutive case system.
    Word order is flexible but SOV is the pragmatically neutral order. -/
def basque : BasicOrderProfile :=
  { language := "Basque"
  , iso := "eus"
  , notes := "SOV dominant; ergative-absolutive case" }

-- ---- SVO languages ----

/-- English: rigid SVO with prepositions and relative clause after noun.
    The canonical head-initial language (among non-V-initial types). -/
def english : BasicOrderProfile :=
  { language := "English"
  , iso := "eng"
  , notes := "Rigid SVO; canonical head-initial (non-V-initial)" }

/-- Mandarin Chinese: SVO with prepositions (mostly). Some constructions
    are head-final (relative clause before noun, some postpositions),
    making Mandarin a mixed-headedness language. -/
def mandarinChinese : BasicOrderProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , notes := "SVO but mixed headedness; RelCl-N, some postpositions" }

/-- Russian: SVO as the pragmatically neutral order, but word order is
    relatively free due to rich case morphology. -/
def russian : BasicOrderProfile :=
  { language := "Russian"
  , iso := "rus"
  , notes := "SVO dominant; case morphology allows scrambling" }

/-- Swahili: SVO with prepositions. Bantu language with rich verbal
    agreement that cross-references subject and object. -/
def swahili : BasicOrderProfile :=
  { language := "Swahili"
  , iso := "swh"
  , notes := "SVO; rich verbal agreement cross-referencing S and O" }

/-- Indonesian: SVO with prepositions. Relatively rigid word order
    for an Austronesian language. -/
def indonesian : BasicOrderProfile :=
  { language := "Indonesian"
  , iso := "ind"
  , notes := "SVO; rigid for an Austronesian language" }

-- ---- VSO languages ----

/-- Arabic (Modern Standard): VSO as the classical/formal basic order,
    though SVO is increasingly common in spoken varieties. -/
def arabicMSA : BasicOrderProfile :=
  { language := "Arabic (MSA)"
  , iso := "arb"
  , notes := "VSO classical; SVO common in modern spoken varieties" }

/-- Irish: VSO with prepositions, relative clause after noun. Celtic
    languages are the canonical European VSO family. -/
def irish : BasicOrderProfile :=
  { language := "Irish"
  , iso := "gle"
  , notes := "VSO; Celtic canonical VSO" }

/-- Tagalog: VSO / VOS (verb-initial with flexible S/O ordering).
    WALS classifies as VSO based on pragmatically neutral clauses.
    Philippine-type voice system complicates the S vs O distinction. -/
def tagalog : BasicOrderProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , notes := "VSO; Philippine voice system complicates S/O identification" }

/-- Welsh: VSO with prepositions, relative clause after noun.
    Another Celtic VSO language. -/
def welsh : BasicOrderProfile :=
  { language := "Welsh"
  , iso := "cym"
  , notes := "VSO; Celtic VSO like Irish" }

-- ---- VOS languages ----

/-- Malagasy: VOS with prepositions. The best-known VOS language,
    extensively studied in formal syntax. -/
def malagasy : BasicOrderProfile :=
  { language := "Malagasy"
  , iso := "mlg"
  , notes := "VOS; Austronesian; extensively studied in formal syntax. NOTE: absent from WALS F81A/F82A/F83A; derived order accessors return .noDominant. Reference grammars classify as VOS." }

/-- Tzotzil (Mayan): VOS basic order, common in the Mayan family. -/
def tzotzil : BasicOrderProfile :=
  { language := "Tzotzil"
  , iso := "tzo"
  , notes := "VOS; Mayan family" }

-- ---- OVS languages ----

/-- Hixkaryana (Cariban; Brazil): the first language for which OVS basic
    order was convincingly demonstrated. This discovery
    refuted the earlier claim that OVS and OSV orders were unattested. -/
def hixkaryana : BasicOrderProfile :=
  { language := "Hixkaryana"
  , iso := "hix"
  , notes := "OVS; first demonstrated by Derbyshire (1977); Cariban" }

-- ---- No dominant order ----

/-- German: V2 in main clauses, SOV in embedded clauses. WALS classifies
    as SVO, but many syntacticians analyze the underlying order as SOV
    with V2 movement. The tension makes "no dominant order" defensible
    (though WALS itself codes German as SVO). -/
def germanV2 : BasicOrderProfile :=
  { language := "German"
  , iso := "deu"
  , notes := "V2 main clauses, SOV embedded; WALS codes as noDominant for F81A and F83A, SV for F82A" }

/-- Warlpiri (Pama-Nyungan; Australia): radically free word order, with
    all six permutations of S, O, V attested in natural discourse.
    The canonical non-configurational language. -/
def warlpiri : BasicOrderProfile :=
  { language := "Warlpiri"
  , iso := "wbp"
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

end Phenomena.WordOrder.Typology
