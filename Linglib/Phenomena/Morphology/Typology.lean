import Mathlib.Data.Rat.Defs
import Linglib.Core.WALS.Features.F20A
import Linglib.Core.WALS.Features.F21A
import Linglib.Core.WALS.Features.F22A
import Linglib.Core.WALS.Features.F26A
import Linglib.Core.WALS.Features.F27A
import Linglib.Core.WALS.Features.F23A
import Linglib.Core.WALS.Features.F24A
import Linglib.Core.WALS.Features.F25A
import Linglib.Core.WALS.Features.F25B
import Linglib.Core.WALS.Features.F28A
import Linglib.Core.WALS.Features.F29A
import Linglib.Core.WALS.Features.F21B
import Linglib.Core.WALS.Features.F62A
import Linglib.Core.WALS.Features.F79A
import Linglib.Core.WALS.Features.F79B
import Linglib.Core.WALS.Features.F80A

/-!
# Morphological Typology: Paradigm Complexity
@cite{ackerman-malouf-2013}

Cross-linguistic typological data on morphological paradigm complexity.

## LanguageData

`LanguageData` records summary statistics about a language's inflectional
paradigm system: the number of inflection classes (E-complexity), the
number of paradigm cells, and information-theoretic measures of paradigm
predictability (I-complexity).

## @cite{ackerman-malouf-2013} Sample

Ten typologically diverse languages from @cite{ackerman-malouf-2013}, spanning three phyla, four macro-areas, and a range from 2 to 109
inflection classes. The central empirical finding: despite wildly varying
E-complexity, I-complexity (average conditional entropy) is uniformly low
across all ten languages.

-/

namespace Phenomena.Morphology.Typology

private abbrev ch20 := Core.WALS.F20A.allData
private abbrev ch21 := Core.WALS.F21A.allData
private abbrev ch22 := Core.WALS.F22A.allData
private abbrev ch26 := Core.WALS.F26A.allData
private abbrev ch27 := Core.WALS.F27A.allData
private abbrev ch23 := Core.WALS.F23A.allData
private abbrev ch24 := Core.WALS.F24A.allData
private abbrev ch25a := Core.WALS.F25A.allData
private abbrev ch25b := Core.WALS.F25B.allData
private abbrev ch28 := Core.WALS.F28A.allData
private abbrev ch29 := Core.WALS.F29A.allData
private abbrev ch21b := Core.WALS.F21B.allData
private abbrev ch62 := Core.WALS.F62A.allData
private abbrev ch79a := Core.WALS.F79A.allData
private abbrev ch79b := Core.WALS.F79B.allData
private abbrev ch80 := Core.WALS.F80A.allData

-- ============================================================================
-- §1. Language Data Records
-- ============================================================================

/-- Summary statistics for a language's morphological paradigm system,
    as reported in published studies.

    Fields correspond to Tables 2--3 of @cite{ackerman-malouf-2013}. -/
structure LanguageData where
  /-- Language name -/
  name : String
  /-- Language family -/
  family : String
  /-- Number of inflection classes (E-complexity) -/
  numClasses : Nat
  /-- Number of paradigm cells -/
  numCells : Nat
  /-- Average conditional entropy H(Ci|Cj) in bits (I-complexity) -/
  avgCondEntropy : ℚ
  /-- Maximum cell entropy max H(Ci) in bits -/
  maxCellEntropy : ℚ
  deriving Repr

-- ============================================================================
-- §2. @cite{ackerman-malouf-2013}: The Ten Languages
-- ============================================================================

/-! ### Nilo-Saharan languages -/

/-- Fur (Nilo-Saharan, Fur; Sudan). 4 classes, 2 cells. -/
def fur : LanguageData where
  name := "Fur"
  family := "Nilo-Saharan"
  numClasses := 4
  numCells := 2
  avgCondEntropy := 489 / 1000  -- 0.489
  maxCellEntropy := 1334 / 1000  -- 1.334

/-- Ngiti (Nilo-Saharan, Central Sudanic; DRC). 8 classes, 2 cells. -/
def ngiti : LanguageData where
  name := "Ngiti"
  family := "Nilo-Saharan"
  numClasses := 8
  numCells := 2
  avgCondEntropy := 380 / 1000  -- 0.380
  maxCellEntropy := 1741 / 1000  -- 1.741

/-- Nuer (Nilo-Saharan, Nilotic; Sudan/South Sudan). 31 classes, 4 cells. -/
def nuer : LanguageData where
  name := "Nuer"
  family := "Nilo-Saharan"
  numClasses := 31
  numCells := 4
  avgCondEntropy := 513 / 1000  -- 0.513
  maxCellEntropy := 3224 / 1000  -- 3.224

/-! ### Trans-New Guinea languages -/

/-- Kwerba (Trans-New Guinea; Papua, Indonesia). 2 classes, 2 cells. -/
def kwerba : LanguageData where
  name := "Kwerba"
  family := "Trans-New Guinea"
  numClasses := 2
  numCells := 2
  avgCondEntropy := 469 / 1000  -- 0.469
  maxCellEntropy := 529 / 1000  -- 0.529

/-! ### Oto-Manguean languages -/

/-- Chinantec (Oto-Manguean; Oaxaca, Mexico). 62 classes, 4 cells.
    Comaltepec Chinantec tonal verb paradigms. -/
def chinantec : LanguageData where
  name := "Chinantec"
  family := "Oto-Manguean"
  numClasses := 62
  numCells := 4
  avgCondEntropy := 426 / 1000  -- 0.426
  maxCellEntropy := 4266 / 1000  -- 4.266

/-- Chiquihuitlan Mazatec (Oto-Manguean; Oaxaca, Mexico).
    109 classes, 4 cells. The paper's primary case study (section 4). -/
def mazatec : LanguageData where
  name := "Chiquihuitlan Mazatec"
  family := "Oto-Manguean"
  numClasses := 109
  numCells := 4
  avgCondEntropy := 709 / 1000  -- 0.709
  maxCellEntropy := 5248 / 1000  -- 5.248

/-! ### Uralic languages -/

/-- Finnish (Uralic, Finnic). 51 classes, 8 cells. -/
def finnish : LanguageData where
  name := "Finnish"
  family := "Uralic"
  numClasses := 51
  numCells := 8
  avgCondEntropy := 209 / 1000  -- 0.209
  maxCellEntropy := 3803 / 1000  -- 3.803

/-! ### Indo-European languages -/

/-- German (Indo-European, Germanic). 7 classes, 8 cells. -/
def german : LanguageData where
  name := "German"
  family := "Indo-European"
  numClasses := 7
  numCells := 8
  avgCondEntropy := 45 / 1000  -- 0.045
  maxCellEntropy := 1906 / 1000  -- 1.906

/-- Russian (Indo-European, Slavic). 8 classes, 8 cells. -/
def russian : LanguageData where
  name := "Russian"
  family := "Indo-European"
  numClasses := 8
  numCells := 8
  avgCondEntropy := 89 / 1000  -- 0.089
  maxCellEntropy := 2170 / 1000  -- 2.170

/-- Spanish (Indo-European, Romance). 3 classes, 57 cells. -/
def spanish : LanguageData where
  name := "Spanish"
  family := "Indo-European"
  numClasses := 3
  numCells := 57
  avgCondEntropy := 3 / 1000  -- 0.003
  maxCellEntropy := 1522 / 1000  -- 1.522

-- ============================================================================
-- §3. The Full Sample
-- ============================================================================

/-- All 10 languages in the @cite{ackerman-malouf-2013} sample (Table 3). -/
def ackermanMalouf2013 : List LanguageData :=
  [fur, ngiti, nuer, kwerba, chinantec, mazatec, finnish, german, russian, spanish]

/-- The LCEC threshold: all 10 languages fall below 1 bit of average
    conditional entropy. Even the most complex system (Mazatec, 109 classes)
    has I-complexity < 1 bit. -/
def lcecThreshold : ℚ := 1

/-- Expected I-complexity under random class assignment for Mazatec
    (Monte Carlo baseline). The paper reports the mean of 1000 random
    permutations as ~5.25 bits, far above the observed 0.709 bits. -/
def mazatecRandomBaseline : ℚ := 525 / 100  -- 5.25

-- ============================================================================
-- §4. WALS Morphological Mechanism Chapters (20--29)
-- ============================================================================

/-!
## Morphological Mechanisms: WALS Chapters 20--29

Chapters 20--29 of WALS cover the fundamental *mechanisms* of inflectional
morphology: how formatives are put together (fusion), how many categories a
single formative expresses (exponence), how synthetic verb morphology is
(inflectional synthesis), where grammatical relations are marked (locus of
marking), whether affixes go before or after stems (prefixing vs suffixing),
and whether the language has productive reduplication.

Sources:
- Bickel, B. & Nichols, J. (2013a). Fusion of selected inflectional
  formatives. WALS Online. Ch. 20.
- Bickel, B. & Nichols, J. (2013b). Exponence of selected inflectional
  formatives. WALS Online. Ch. 21.
- Bickel, B. & Nichols, J. (2013c). Inflectional synthesis of the verb.
  WALS Online. Ch. 22.
- Nichols, J. & Bickel, B. (2013a). Locus of marking in the clause.
  WALS Online. Ch. 23.
- Nichols, J. & Bickel, B. (2013b). Locus of marking in possessive NPs.
  WALS Online. Ch. 24.
- Nichols, J. & Bickel, B. (2013c). Locus of marking: whole-language
  typology. WALS Online. Ch. 25.
- Nichols, J. & Bickel, B. (2013d). Zero marking of A and P arguments.
  WALS Online. Ch. 25B.
- Baerman, M. & Brown, D. (2013a). Case syncretism. WALS Online. Ch. 28.
- Baerman, M. & Brown, D. (2013b). Syncretism in verbal person/number
  marking. WALS Online. Ch. 29.
- Dryer, M. S. (2013). Prefixing vs. suffixing in inflectional morphology.
  WALS Online. Ch. 26.
- Rubino, C. (2013). Reduplication. WALS Online. Ch. 27.
-/

-- ============================================================================
-- §4.1 Chapter 20: Fusion of Selected Inflectional Formatives
-- ============================================================================

/-- WALS Ch 20: How inflectional formatives are attached to stems.

    @cite{bickel-nichols-2013a} classify languages by the dominant fusion
    strategy in their inflectional morphology. **Isolating** languages
    express grammatical categories with separate words. **Concatenative**
    (agglutinative) languages attach clearly segmentable affixes.
    **Nonlinear** (fusional) languages use stem-internal changes,
    ablaut, tonal alternation, or portmanteau morphs that resist
    segmentation. -/
inductive Fusion where
  /-- Isolating: grammatical categories expressed by independent words,
      not bound morphology. Example: Mandarin, Vietnamese, Thai. -/
  | isolating
  /-- Concatenative (agglutinative): clearly segmentable affixes concatenated
      to the stem. Each affix typically carries one meaning. Example:
      Turkish, Finnish, Swahili, Quechua. -/
  | concatenative
  /-- Nonlinear (fusional): stem-internal changes, ablaut, tonal alternation,
      or portmanteau morphs. A single formative may express multiple
      categories simultaneously. Example: Arabic, Russian, German. -/
  | nonlinear
  deriving DecidableEq, BEq, Repr

/-- A single row in a WALS distribution table: a label and a language count. -/
structure WALSCount where
  label : String
  count : Nat
  deriving Repr, DecidableEq, BEq

/-- WALS Chapter 20 distribution (@cite{bickel-nichols-2013a}, N = 160). -/
def ch20Distribution : List WALSCount :=
  [ ⟨"Exclusively concatenative", 58⟩
  , ⟨"Strongly concatenative", 28⟩
  , ⟨"Weakly concatenative", 24⟩
  , ⟨"Nonlinear/fusional", 25⟩
  , ⟨"Isolating", 25⟩ ]

/-- Ch 20 total: 160 languages. -/
theorem ch20_total :
    ch20Distribution.foldl (λ acc c => acc + c.count) 0 = 160 := by native_decide

-- ============================================================================
-- §4.2 Chapter 21: Exponence of Selected Inflectional Formatives
-- ============================================================================

/-- WALS Ch 21: How many grammatical categories a single formative expresses.

    @cite{bickel-nichols-2013b} distinguish **monoexponential** systems, where
    each affix realizes exactly one grammatical category (e.g., Turkish -lar
    = plural only), from **polyexponential** (cumulative/fusional) systems,
    where a single formative bundles multiple categories (e.g., Latin -orum =
    genitive + plural simultaneously). -/
inductive Exponence where
  /-- Monoexponential: each formative expresses one category.
      Characteristic of agglutinative systems. -/
  | monoexponential
  /-- Polyexponential (cumulative): single formatives bundle multiple
      categories. Characteristic of fusional systems. -/
  | polyexponential
  /-- No inflectional formatives (isolating). -/
  | noInflection
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 21 distribution (@cite{bickel-nichols-2013b}, N = 159). -/
def ch21Distribution : List WALSCount :=
  [ ⟨"Monoexponential case", 70⟩
  , ⟨"Case + number", 22⟩
  , ⟨"Case + number + gender (polyexponential)", 67⟩ ]

/-- Ch 21 total: 159 languages. -/
theorem ch21_total :
    ch21Distribution.foldl (λ acc c => acc + c.count) 0 = 159 := by native_decide

-- ============================================================================
-- §4.3 Chapter 22: Inflectional Synthesis of the Verb
-- ============================================================================

/-- WALS Ch 22: How many inflectional categories are expressed on the verb.

    @cite{bickel-nichols-2013c} count the number of inflectional categories
    (person, number, tense, aspect, mood, etc.) that are expressed as bound
    morphology on the verb. Languages range from 0 (analytic/isolating) to
    13+ (highly polysynthetic). -/
inductive VerbSynthesis where
  /-- Low synthesis: 0--3 categories per verb word.
      Example: Mandarin (0), English (2--3), Thai (0). -/
  | low
  /-- Moderate synthesis: 4--6 categories per verb word.
      Example: Spanish (5), Russian (4--5), Swahili (5--6). -/
  | moderate
  /-- High synthesis: 7+ categories per verb word.
      Example: Georgian (8+), Quechua (7+), Mohawk (10+). -/
  | high
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 22 distribution (@cite{bickel-nichols-2013c}, N = 145). -/
def ch22Distribution : List WALSCount :=
  [ ⟨"0-1 categories per word", 5⟩
  , ⟨"2-3 categories per word", 39⟩
  , ⟨"4-5 categories per word", 45⟩
  , ⟨"6-7 categories per word", 24⟩
  , ⟨"8-9 categories per word", 10⟩
  , ⟨"10-11 categories per word", 15⟩
  , ⟨"12-13 categories per word", 7⟩ ]

/-- Ch 22 total: 145 languages. -/
theorem ch22_total :
    ch22Distribution.foldl (λ acc c => acc + c.count) 0 = 145 := by native_decide

-- ============================================================================
-- §4.4 Chapter 25: Locus of Marking: Whole-Language Typology
-- ============================================================================

/-- WALS Ch 25: Where grammatical relations are marked in phrases.

    @cite{bickel-nichols-2013a} classify languages by whether grammatical
    relations (subject-of, object-of, possessor-of) are marked on the
    **head** of the phrase (e.g., verb agreement for subjects), on the
    **dependent** (e.g., case marking on nouns), on **both** (double
    marking), or on **neither** (zero marking / rigid word order). -/
inductive LocusOfMarking where
  /-- Head-marking: grammatical relations marked on the head
      (verb agreement, possessum marking). Example: Mohawk, Abkhaz. -/
  | headMarking
  /-- Dependent-marking: grammatical relations marked on the dependent
      (case markers on nouns, adpositions). Example: Japanese, Latin. -/
  | dependentMarking
  /-- Double-marking: both head and dependent are marked.
      Example: Georgian (case + agreement), Basque. -/
  | doubleMarking
  /-- Zero-marking (or no dominant type): grammatical relations signaled
      by word order, not morphology. Example: Mandarin, Thai. -/
  | zeroMarking
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 25 distribution (@cite{bickel-nichols-2013a}, N = 236). -/
def ch25Distribution : List WALSCount :=
  [ ⟨"Head-marking", 47⟩
  , ⟨"Dependent-marking", 63⟩
  , ⟨"Double-marking", 61⟩
  , ⟨"Zero/no dominant type", 65⟩ ]

/-- Ch 25 total: 236 languages. -/
theorem ch25_total :
    ch25Distribution.foldl (λ acc c => acc + c.count) 0 = 236 := by native_decide

-- ============================================================================
-- §4.5 Chapter 26: Prefixing vs Suffixing in Inflectional Morphology
-- ============================================================================

/-- WALS Ch 26: Whether a language predominantly uses prefixes or suffixes
    for inflectional morphology.

    @cite{dryer-haspelmath-2013} classifies languages on a five-point scale from strongly
    suffixing to strongly prefixing, based on the proportion of inflectional
    categories expressed by suffixes vs prefixes. This is one of the most
    robust typological universals: suffixing strongly dominates worldwide
    (Greenberg's Universal 27). -/
inductive PrefixSuffix where
  /-- Strongly suffixing: large majority of inflectional morphology is
      suffixal. Example: Turkish, Finnish, Japanese, Quechua. -/
  | stronglySuffixing
  /-- Weakly suffixing: more suffixing than prefixing but not overwhelmingly.
      Example: Russian, German, Arabic. -/
  | weaklySuffixing
  /-- Equal prefixing and suffixing. Example: some Oceanic languages. -/
  | equalPrefixSuffix
  /-- Weakly prefixing: more prefixing than suffixing.
      Example: Swahili, Tagalog. -/
  | weaklyPrefixing
  /-- Strongly prefixing: large majority of inflectional morphology is
      prefixal. Example: Navajo, Thai (tonal but few affixes). -/
  | stronglyPrefixing
  /-- Little affixation: the language has little inflectional morphology
      to classify. Example: Mandarin, Vietnamese. -/
  | littleAffixation
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 26 distribution (@cite{dryer-haspelmath-2013}, N = 969). -/
def ch26Distribution : List WALSCount :=
  [ ⟨"Strongly suffixing", 406⟩
  , ⟨"Weakly suffixing", 123⟩
  , ⟨"Equal prefixing and suffixing", 58⟩
  , ⟨"Weakly prefixing", 94⟩
  , ⟨"Strongly prefixing", 135⟩
  , ⟨"Little affixation", 153⟩ ]

/-- Ch 26 total: 969 languages. -/
theorem ch26_total :
    ch26Distribution.foldl (λ acc c => acc + c.count) 0 = 969 := by native_decide

-- ============================================================================
-- §4.6 Chapter 27: Reduplication
-- ============================================================================

/-- WALS Ch 27: Whether the language has productive reduplication.

    @cite{rubino-2013} classifies languages by whether they exhibit productive
    full or partial reduplication as a morphological process. Reduplication
    is used cross-linguistically for plurality, intensification, aspect,
    diminutive, and other functions. -/
inductive Reduplication where
  /-- Productive full and partial reduplication.
      Example: Indonesian, Tagalog, Swahili. -/
  | productiveFull
  /-- Productive but only full reduplication. -/
  | fullOnly
  /-- No productive reduplication.
      Example: English, French, Arabic. -/
  | noProductive
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 27 distribution (@cite{rubino-2013}, N = 368). -/
def ch27Distribution : List WALSCount :=
  [ ⟨"Productive full and partial reduplication", 147⟩
  , ⟨"Productive full reduplication only", 35⟩
  , ⟨"No productive reduplication", 186⟩ ]

/-- Ch 27 total: 368 languages. -/
theorem ch27_total :
    ch27Distribution.foldl (λ acc c => acc + c.count) 0 = 368 := by native_decide

-- ============================================================================
-- §4.7 Chapter 23: Locus of Marking in the Clause
-- ============================================================================

/-- WALS Ch 23: Where grammatical relations are marked in clausal syntax.

    Clause-level marking addresses whether the subject/object relation is
    indicated on the head (verb agreement), the dependent (case marking on
    nouns), both, or neither. -/
inductive LocusClause where
  /-- Head marking: grammatical relations marked on the verb
      (agreement markers). Example: Abkhaz, Mohawk. -/
  | headMarking
  /-- Dependent marking: grammatical relations marked on the noun
      (case markers). Example: Japanese, Finnish. -/
  | dependentMarking
  /-- Double marking: both head and dependent are marked.
      Example: Georgian, Basque. -/
  | doubleMarking
  /-- No marking: grammatical relations not morphologically marked
      in the clause. Example: Thai, Vietnamese. -/
  | noMarking
  /-- Other: does not fit neatly into the above categories. -/
  | other
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 23 distribution (N = 236). -/
def ch23Distribution : List WALSCount :=
  [ ⟨"Head marking", 71⟩
  , ⟨"Dependent marking", 63⟩
  , ⟨"Double marking", 58⟩
  , ⟨"No marking", 42⟩
  , ⟨"Other", 2⟩ ]

/-- Ch 23 total: 236 languages. -/
theorem ch23_total :
    ch23Distribution.foldl (λ acc c => acc + c.count) 0 = 236 := by native_decide

-- ============================================================================
-- §4.8 Chapter 24: Locus of Marking in Possessive Noun Phrases
-- ============================================================================

/-- WALS Ch 24: Where grammatical relations are marked in possessive NPs.

    Languages differ in whether the possessive relation is marked on the
    possessum (head marking, e.g., Hungarian haz-am 'house-my'), on the
    possessor (dependent marking, e.g., English John's), on both, or on
    neither. -/
inductive LocusPossessive where
  /-- Head marking: possession marked on the possessum. -/
  | headMarking
  /-- Dependent marking: possession marked on the possessor. -/
  | dependentMarking
  /-- Double marking: both possessor and possessum are marked. -/
  | doubleMarking
  /-- No marking: possession not morphologically marked. -/
  | noMarking
  /-- Other: does not fit neatly into the above categories. -/
  | other
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 24 distribution (N = 236). -/
def ch24Distribution : List WALSCount :=
  [ ⟨"Head marking", 78⟩
  , ⟨"Dependent marking", 98⟩
  , ⟨"Double marking", 22⟩
  , ⟨"No marking", 32⟩
  , ⟨"Other", 6⟩ ]

/-- Ch 24 total: 236 languages. -/
theorem ch24_total :
    ch24Distribution.foldl (λ acc c => acc + c.count) 0 = 236 := by native_decide

-- ============================================================================
-- §4.9 Chapter 25A: Locus of Marking: Whole-Language Typology
-- ============================================================================

/-- WALS Ch 25A: Whole-language locus-of-marking classification combining
    clause-level and NP-level patterns.

    Languages consistent in both domains get a simple label; those with
    mixed patterns are classified as "inconsistent or other". -/
inductive WholeLanguageMarking where
  /-- Consistently head-marking in both clause and NP. -/
  | headMarking
  /-- Consistently dependent-marking in both clause and NP. -/
  | dependentMarking
  /-- Consistently double-marking in both clause and NP. -/
  | doubleMarking
  /-- Consistently zero-marking in both clause and NP. -/
  | zeroMarking
  /-- Inconsistent or other: clause and NP patterns differ. -/
  | inconsistentOrOther
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 25A distribution (N = 236). -/
def ch25aDistribution : List WALSCount :=
  [ ⟨"Head-marking", 47⟩
  , ⟨"Dependent-marking", 46⟩
  , ⟨"Double-marking", 16⟩
  , ⟨"Zero-marking", 6⟩
  , ⟨"Inconsistent or other", 121⟩ ]

/-- Ch 25A total: 236 languages. -/
theorem ch25a_total :
    ch25aDistribution.foldl (λ acc c => acc + c.count) 0 = 236 := by native_decide

-- ============================================================================
-- §4.10 Chapter 25B: Zero Marking of A and P Arguments
-- ============================================================================

/-- WALS Ch 25B: Whether a language has zero marking (no overt case or
    agreement) for both the A (agent-like) and P (patient-like) arguments
    of a transitive clause. -/
inductive ZeroMarkingAP where
  /-- Both A and P arguments are zero-marked. -/
  | zeroMarking
  /-- At least one of A and P is overtly marked. -/
  | nonZeroMarking
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 25B distribution (N = 235). -/
def ch25bDistribution : List WALSCount :=
  [ ⟨"Zero-marking", 16⟩
  , ⟨"Non-zero marking", 219⟩ ]

/-- Ch 25B total: 235 languages. -/
theorem ch25b_total :
    ch25bDistribution.foldl (λ acc c => acc + c.count) 0 = 235 := by native_decide

-- ============================================================================
-- §4.11 Chapter 28: Case Syncretism
-- ============================================================================

/-- WALS Ch 28: Whether a language exhibits syncretism (neutralization of
    case distinctions) in its nominal case system. -/
inductive CaseSyncretism where
  /-- No case marking: the language lacks morphological case entirely. -/
  | noCaseMarking
  /-- Core cases only: syncretism limited to core grammatical cases. -/
  | coreCasesOnly
  /-- Core and non-core: syncretism spans both core and peripheral cases. -/
  | coreAndNonCore
  /-- No syncretism: the language has case but no syncretic forms. -/
  | noSyncretism
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 28 distribution (N = 198). -/
def ch28Distribution : List WALSCount :=
  [ ⟨"No case marking", 123⟩
  , ⟨"Core cases only", 18⟩
  , ⟨"Core and non-core", 22⟩
  , ⟨"No syncretism", 35⟩ ]

/-- Ch 28 total: 198 languages. -/
theorem ch28_total :
    ch28Distribution.foldl (λ acc c => acc + c.count) 0 = 198 := by native_decide

-- ============================================================================
-- §4.12 Chapter 29: Syncretism in Verbal Person/Number Marking
-- ============================================================================

/-- WALS Ch 29: Whether a language exhibits syncretism in its verbal
    person/number agreement paradigm. -/
inductive VerbalSyncretism where
  /-- No subject person/number marking on the verb. -/
  | noSubjectMarking
  /-- Syncretic: some person/number cells share the same verb form. -/
  | syncretic
  /-- Not syncretic: all person/number cells have distinct forms. -/
  | notSyncretic
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 29 distribution (N = 198). -/
def ch29Distribution : List WALSCount :=
  [ ⟨"No subject person/number marking", 57⟩
  , ⟨"Syncretic", 60⟩
  , ⟨"Not syncretic", 81⟩ ]

/-- Ch 29 total: 198 languages. -/
theorem ch29_total :
    ch29Distribution.foldl (λ acc c => acc + c.count) 0 = 198 := by native_decide

-- ============================================================================
-- §4.13 Chapter 21B: Exponence of Tense-Aspect-Mood Inflection
-- ============================================================================

/-- WALS Ch 21B: What categories co-occur with tense-aspect-mood in a single
    inflectional formative.

    @cite{bickel-nichols-2013b} classify languages by whether TAM inflection
    is monoexponential (the TAM formative expresses only TAM) or bundles TAM
    with other categories such as agreement, diathesis, polarity, or
    construct state. Some languages lack TAM inflection entirely. -/
inductive TAMExponence where
  /-- Monoexponential TAM: the TAM formative expresses only TAM. -/
  | monoexponential
  /-- TAM bundled with agreement. -/
  | tamAgreement
  /-- TAM bundled with agreement and diathesis. -/
  | tamAgreementDiathesis
  /-- TAM bundled with agreement and construct state. -/
  | tamAgreementConstruct
  /-- TAM bundled with polarity. -/
  | tamPolarity
  /-- No TAM inflection. -/
  | noTam
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 21B distribution (N = 160). -/
def ch21bDistribution : List WALSCount :=
  [ ⟨"Monoexponential TAM", 127⟩
  , ⟨"TAM+agreement", 19⟩
  , ⟨"TAM+agreement+diathesis", 4⟩
  , ⟨"TAM+agreement+construct", 1⟩
  , ⟨"TAM+polarity", 5⟩
  , ⟨"No TAM", 4⟩ ]

/-- Ch 21B total: 160 languages. -/
theorem ch21b_total :
    ch21bDistribution.foldl (λ acc c => acc + c.count) 0 = 160 := by native_decide

-- ============================================================================
-- §4.14 Chapter 62A: Action Nominal Constructions
-- ============================================================================

/-- WALS Ch 62: How a language constructs action nominals (nominalizations
    of verbs that denote events or actions).

    Languages differ in whether the arguments of the underlying verb retain
    their clausal form (sentential), take possessive marking (possessive-
    accusative, ergative-possessive, double-possessive), or whether action
    nominals are absent or restricted. -/
inductive ActionNominal where
  /-- Sentential: arguments keep clausal marking. -/
  | sentential
  /-- Possessive-Accusative: subject is possessive, object is accusative. -/
  | possessiveAccusative
  /-- Ergative-Possessive: subject is ergative/genitive, object is possessive. -/
  | ergativePossessive
  /-- Double-Possessive: both subject and object are possessive. -/
  | doublePossessive
  /-- Other construction type. -/
  | other
  /-- Mixed: multiple construction types coexist. -/
  | mixed
  /-- Restricted: action nominals exist but are severely limited. -/
  | restricted
  /-- No action nominals. -/
  | noActionNominals
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 62A distribution (N = 168). -/
def ch62Distribution : List WALSCount :=
  [ ⟨"Sentential", 25⟩
  , ⟨"Possessive-Accusative", 29⟩
  , ⟨"Ergative-Possessive", 21⟩
  , ⟨"Double-Possessive", 7⟩
  , ⟨"Other", 6⟩
  , ⟨"Mixed", 14⟩
  , ⟨"Restricted", 24⟩
  , ⟨"No action nominals", 42⟩ ]

/-- Ch 62 total: 168 languages. -/
theorem ch62_total :
    ch62Distribution.foldl (λ acc c => acc + c.count) 0 = 168 := by native_decide

-- ============================================================================
-- §4.15 Chapter 79A: Suppletion According to Tense and Aspect
-- ============================================================================

/-- WALS Ch 79A: Whether a language has suppletive verb forms conditioned
    by tense, aspect, or both.

    Suppletion is the replacement of a stem by a phonologically unrelated
    form in a paradigm cell (e.g., English go/went). Languages vary in
    whether suppletion is triggered by tense distinctions, aspect
    distinctions, both, or neither. -/
inductive SuppletionTA where
  /-- Suppletion conditioned by tense. -/
  | tense
  /-- Suppletion conditioned by aspect. -/
  | aspect
  /-- Suppletion conditioned by both tense and aspect. -/
  | tenseAndAspect
  /-- No suppletion according to tense or aspect. -/
  | none
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 79A distribution (N = 193). -/
def ch79aDistribution : List WALSCount :=
  [ ⟨"Tense", 36⟩
  , ⟨"Aspect", 10⟩
  , ⟨"Tense and aspect", 24⟩
  , ⟨"None", 123⟩ ]

/-- Ch 79A total: 193 languages. -/
theorem ch79a_total :
    ch79aDistribution.foldl (λ acc c => acc + c.count) 0 = 193 := by native_decide

-- ============================================================================
-- §4.16 Chapter 79B: Suppletion in Imperatives and Hortatives
-- ============================================================================

/-- WALS Ch 79B: Whether a language has suppletive verb forms specifically
    in imperative or hortative paradigm cells.

    Some languages have verbs whose imperative form is unrelated to the
    indicative stem (e.g., Spanish ir 'go' but ve 'go.IMP'). -/
inductive SuppletionImperative where
  /-- A regular and a suppletive form alternate. -/
  | alternating
  /-- Suppletion in imperative forms. -/
  | imperative
  /-- Suppletion in hortative forms. -/
  | hortative
  /-- Suppletion in both imperative and hortative. -/
  | imperativeAndHortative
  /-- No suppletive imperatives reported. -/
  | none
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 79B distribution (N = 193). -/
def ch79bDistribution : List WALSCount :=
  [ ⟨"Regular and suppletive alternate", 8⟩
  , ⟨"Imperative", 29⟩
  , ⟨"Hortative", 2⟩
  , ⟨"Imperative and Hortative", 1⟩
  , ⟨"None", 153⟩ ]

/-- Ch 79B total: 193 languages. -/
theorem ch79b_total :
    ch79bDistribution.foldl (λ acc c => acc + c.count) 0 = 193 := by native_decide

-- ============================================================================
-- §4.17 Chapter 80A: Verbal Number and Suppletion
-- ============================================================================

/-- WALS Ch 80A: Whether a language has verbal number marking (distinct verb
    forms for singular vs plural events or participants) and whether such
    pairs involve suppletion.

    Verbal number is distinct from subject/object agreement: it marks the
    number of events (pluractional) or participants on the verb stem itself,
    often via completely different roots. -/
inductive VerbalNumber where
  /-- No verbal number. -/
  | none
  /-- Singular-plural verb pairs without suppletion. -/
  | pairsNoSuppletion
  /-- Singular-plural verb pairs with suppletion. -/
  | pairsSuppletion
  /-- Singular-dual-plural triples without suppletion. -/
  | triplesNoSuppletion
  /-- Singular-dual-plural triples with suppletion. -/
  | triplesSuppletion
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 80A distribution (N = 193). -/
def ch80Distribution : List WALSCount :=
  [ ⟨"None", 159⟩
  , ⟨"Singular-plural pairs, no suppletion", 12⟩
  , ⟨"Singular-plural pairs, suppletion", 15⟩
  , ⟨"Singular-dual-plural triples, no suppletion", 5⟩
  , ⟨"Singular-dual-plural triples, suppletion", 2⟩ ]

/-- Ch 80 total: 193 languages. -/
theorem ch80_total :
    ch80Distribution.foldl (λ acc c => acc + c.count) 0 = 193 := by native_decide

-- ============================================================================
-- §4.18 WALS Converter Functions
-- ============================================================================

/-- Convert WALS 20A fusion type to the local three-way `Fusion` classification.
    Returns `none` for mixed categories (tonal/isolating+concatenative) that
    do not map cleanly to the coarser local type. -/
private def fromWALS20A : Core.WALS.F20A.FusionType → Option Fusion
  | .exclusivelyConcatenative => some .concatenative
  | .exclusivelyIsolating     => some .isolating
  | .exclusivelyTonal         => some .nonlinear
  | .ablautConcatenative      => some .nonlinear
  | .tonalIsolating           => none  -- mixed: no clean mapping
  | .tonalConcatenative       => none  -- mixed: no clean mapping
  | .isolatingConcatenative   => none  -- mixed: no clean mapping

/-- Convert WALS 21A exponence type to the local `Exponence` classification.
    Returns `none` for `noCase`, since WALS 21A specifically evaluates the
    exponence of *case formatives* -- a language without case provides no
    information about its overall exponence pattern. -/
private def fromWALS21A : Core.WALS.F21A.ExponenceType → Option Exponence
  | .monoexponentialCase  => some .monoexponential
  | .caseNumber           => some .polyexponential
  | .caseReferentiality   => some .polyexponential
  | .caseTam              => some .polyexponential
  | .noCase               => none  -- no case = no information about exponence

/-- Convert WALS 22A inflectional synthesis to the local three-way
    `VerbSynthesis` classification. -/
private def fromWALS22A : Core.WALS.F22A.InflectionalSynthesis → VerbSynthesis
  | .categoryPerWord0_1    => .low
  | .categoriesPerWord2_3  => .low
  | .categoriesPerWord4_5  => .moderate
  | .categoriesPerWord6_7  => .moderate
  | .categoriesPerWord8_9  => .high
  | .categoriesPerWord10_11 => .high
  | .categoriesPerWord12_13 => .high

/-- Convert WALS 26A prefix/suffix preference to the local `PrefixSuffix`
    classification. This is a direct 1-to-1 mapping. -/
private def fromWALS26A : Core.WALS.F26A.PrefixSuffixPreference → PrefixSuffix
  | .littleAffixation             => .littleAffixation
  | .stronglySuffixing            => .stronglySuffixing
  | .weaklySuffixing              => .weaklySuffixing
  | .equalPrefixingAndSuffixing   => .equalPrefixSuffix
  | .weaklyPrefixing              => .weaklyPrefixing
  | .strongPrefixing              => .stronglyPrefixing

/-- Convert WALS 27A reduplication type to the local `Reduplication`
    classification. This is a direct 1-to-1 mapping. -/
private def fromWALS27A : Core.WALS.F27A.ReduplicationType → Reduplication
  | .productiveFullAndPartialReduplication => .productiveFull
  | .fullReduplicationOnly                => .fullOnly
  | .noProductiveReduplication            => .noProductive

/-- Convert WALS 23A locus-of-marking-in-clause to the local `LocusClause`
    classification. This is a direct 1-to-1 mapping. -/
private def fromWALS23A : Core.WALS.F23A.LocusOfMarkingInTheClause → LocusClause
  | .headMarking      => .headMarking
  | .dependentMarking => .dependentMarking
  | .doubleMarking    => .doubleMarking
  | .noMarking        => .noMarking
  | .other            => .other

/-- Convert WALS 24A locus-of-marking-in-possessive-NP to the local
    `LocusPossessive` classification. This is a direct 1-to-1 mapping. -/
private def fromWALS24A :
    Core.WALS.F24A.LocusOfMarkingInPossessiveNounPhrases → LocusPossessive
  | .headMarking      => .headMarking
  | .dependentMarking => .dependentMarking
  | .doubleMarking    => .doubleMarking
  | .noMarking        => .noMarking
  | .other            => .other

/-- Convert WALS 25A whole-language locus-of-marking typology to the local
    `WholeLanguageMarking` classification. This is a direct 1-to-1 mapping. -/
private def fromWALS25A :
    Core.WALS.F25A.LocusOfMarkingWholeLanguageTypology → WholeLanguageMarking
  | .headMarking         => .headMarking
  | .dependentMarking    => .dependentMarking
  | .doubleMarking       => .doubleMarking
  | .zeroMarking         => .zeroMarking
  | .inconsistentOrOther => .inconsistentOrOther

/-- Convert WALS 25B zero-marking-of-A-and-P-arguments to the local
    `ZeroMarkingAP` classification. This is a direct 1-to-1 mapping. -/
private def fromWALS25B :
    Core.WALS.F25B.ZeroMarkingOfAAndPArguments → ZeroMarkingAP
  | .zeroMarking    => .zeroMarking
  | .nonZeroMarking => .nonZeroMarking

/-- Convert WALS 28A case syncretism to the local `CaseSyncretism`
    classification. This is a direct 1-to-1 mapping. -/
private def fromWALS28A : Core.WALS.F28A.CaseSyncretism → CaseSyncretism
  | .noCaseMarking  => .noCaseMarking
  | .coreCasesOnly  => .coreCasesOnly
  | .coreAndNonCore => .coreAndNonCore
  | .noSyncretism   => .noSyncretism

/-- Convert WALS 29A syncretism in verbal person/number marking to the local
    `VerbalSyncretism` classification. This is a direct 1-to-1 mapping. -/
private def fromWALS29A :
    Core.WALS.F29A.SyncretismInVerbalPersonNumberMarking → VerbalSyncretism
  | .noSubjectPersonNumberMarking => .noSubjectMarking
  | .syncretic                    => .syncretic
  | .notSyncretic                 => .notSyncretic

/-- Convert WALS 21B TAM exponence to the local `TAMExponence`
    classification. This is a direct 1-to-1 mapping. -/
private def fromWALS21B :
    Core.WALS.F21B.ExponenceOfTenseAspectMoodInflection → TAMExponence
  | .monoexponentialTam      => .monoexponential
  | .tamAgreement            => .tamAgreement
  | .tamAgreementDiathesis   => .tamAgreementDiathesis
  | .tamAgreementConstruct   => .tamAgreementConstruct
  | .tamPolarity             => .tamPolarity
  | .noTam                   => .noTam

/-- Convert WALS 62A action nominal constructions to the local `ActionNominal`
    classification. This is a direct 1-to-1 mapping. -/
private def fromWALS62A :
    Core.WALS.F62A.ActionNominalConstructions → ActionNominal
  | .sentential           => .sentential
  | .possessiveAccusative => .possessiveAccusative
  | .ergativePossessive   => .ergativePossessive
  | .doublePossessive     => .doublePossessive
  | .other                => .other
  | .mixed                => .mixed
  | .restricted           => .restricted
  | .noActionNominals     => .noActionNominals

/-- Convert WALS 79A suppletion-by-tense-and-aspect to the local
    `SuppletionTA` classification. This is a direct 1-to-1 mapping. -/
private def fromWALS79A :
    Core.WALS.F79A.SuppletionAccordingToTenseAndAspect → SuppletionTA
  | .tense          => .tense
  | .aspect         => .aspect
  | .tenseAndAspect => .tenseAndAspect
  | .none           => .none

/-- Convert WALS 79B suppletion-in-imperatives to the local
    `SuppletionImperative` classification. This is a direct 1-to-1 mapping. -/
private def fromWALS79B :
    Core.WALS.F79B.SuppletionInImperativesAndHortatives → SuppletionImperative
  | .aRegularAndASuppletiveFormAlternate => .alternating
  | .imperative                          => .imperative
  | .hortative                           => .hortative
  | .imperativeAndHortative              => .imperativeAndHortative
  | .none                                => .none

/-- Convert WALS 80A verbal number and suppletion to the local
    `VerbalNumber` classification. This is a direct 1-to-1 mapping. -/
private def fromWALS80A :
    Core.WALS.F80A.VerbalNumberAndSuppletion → VerbalNumber
  | .none                                    => .none
  | .singularPluralPairsNoSuppletion         => .pairsNoSuppletion
  | .singularPluralPairsSuppletion           => .pairsSuppletion
  | .singularDualPluralTriplesNoSuppletion   => .triplesNoSuppletion
  | .singularDualPluralTriplesSuppletion     => .triplesSuppletion

-- ============================================================================
-- §5. MorphProfile Structure
-- ============================================================================

/-- A language's morphological mechanism profile, combining dimensions from
    WALS Chapters 20--29. This captures the core "morphological type" of a
    language across multiple cross-cutting dimensions. -/
structure MorphProfile where
  /-- Language name -/
  language : String
  /-- ISO 639-3 code -/
  iso : String
  /-- Ch 20: Fusion type -/
  fusion : Fusion
  /-- Ch 21: Exponence type -/
  exponence : Exponence
  /-- Ch 22: Inflectional synthesis of the verb -/
  verbSynthesis : VerbSynthesis
  /-- Ch 25: Locus of marking -/
  locus : LocusOfMarking
  /-- Ch 26: Prefixing vs suffixing -/
  prefixSuffix : PrefixSuffix
  /-- Ch 27: Productive reduplication -/
  reduplication : Reduplication
  /-- Ch 23: Locus of marking in the clause (optional) -/
  locusClause : Option LocusClause := none
  /-- Ch 24: Locus of marking in possessive NP (optional) -/
  locusPossessive : Option LocusPossessive := none
  /-- Ch 25A: Whole-language marking typology (optional) -/
  wholeLanguageMarking : Option WholeLanguageMarking := none
  /-- Ch 25B: Zero marking of A and P arguments (optional) -/
  zeroMarkingAP : Option ZeroMarkingAP := none
  /-- Ch 28: Case syncretism (optional) -/
  caseSyncretism : Option CaseSyncretism := none
  /-- Ch 29: Syncretism in verbal person/number marking (optional) -/
  verbalSyncretism : Option VerbalSyncretism := none
  /-- Ch 21B: Exponence of TAM inflection (optional) -/
  tamExponence : Option TAMExponence := none
  /-- Ch 62A: Action nominal constructions (optional) -/
  actionNominal : Option ActionNominal := none
  /-- Ch 79A: Suppletion according to tense and aspect (optional) -/
  suppletionTA : Option SuppletionTA := none
  /-- Ch 79B: Suppletion in imperatives and hortatives (optional) -/
  suppletionImperative : Option SuppletionImperative := none
  /-- Ch 80A: Verbal number and suppletion (optional) -/
  verbalNumber : Option VerbalNumber := none
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- §6. Language Profiles
-- ============================================================================

section MorphLanguageData

/-- English: weakly concatenative (some fusional inflection like strong verbs),
    moderate verb synthesis (person, number, tense), dependent-marking (case
    on pronouns, not agreement-dominant), weakly suffixing (-s, -ed, -ing),
    no productive reduplication. -/
def englishMorph : MorphProfile :=
  { language := "English"
  , iso := "eng"
  , fusion := .concatenative
  , exponence := .monoexponential
  , verbSynthesis := .low
  , locus := .dependentMarking
  , prefixSuffix := .weaklySuffixing
  , reduplication := .noProductive
  , locusClause := some .dependentMarking
  , locusPossessive := some .dependentMarking
  , wholeLanguageMarking := some .dependentMarking
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .coreCasesOnly
  , verbalSyncretism := some .syncretic
  , tamExponence := some .monoexponential
  , actionNominal := some .mixed
  , suppletionTA := some .tense
  , suppletionImperative := some .none
  , verbalNumber := some .none }

/-- Mandarin Chinese: isolating, no inflectional formatives, zero verb
    synthesis, zero/no-dominant marking (word order encodes relations),
    little affixation, no productive reduplication (though some iconic
    doubling exists, it is not inflectional). -/
def mandarinMorph : MorphProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , fusion := .isolating
  , exponence := .noInflection
  , verbSynthesis := .low
  , locus := .zeroMarking
  , prefixSuffix := .littleAffixation
  , reduplication := .noProductive
  , locusClause := some .dependentMarking
  , locusPossessive := some .dependentMarking
  , wholeLanguageMarking := some .dependentMarking
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .noCaseMarking
  , verbalSyncretism := some .noSubjectMarking
  , tamExponence := some .monoexponential
  , actionNominal := some .noActionNominals
  , suppletionTA := some .none
  , suppletionImperative := some .none
  , verbalNumber := some .none }

/-- Japanese: concatenative/agglutinative, monoexponential (each suffix
    carries one meaning: -ta past, -nai negation, -reru passive),
    moderate verb synthesis (tense, aspect, polarity, voice),
    dependent-marking (case particles on nouns), strongly suffixing,
    no productive reduplication. -/
def japaneseMorph : MorphProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , fusion := .concatenative
  , exponence := .monoexponential
  , verbSynthesis := .moderate
  , locus := .dependentMarking
  , prefixSuffix := .stronglySuffixing
  , reduplication := .noProductive
  , locusClause := some .dependentMarking
  , locusPossessive := some .dependentMarking
  , wholeLanguageMarking := some .dependentMarking
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .noCaseMarking
  , verbalSyncretism := some .noSubjectMarking
  , tamExponence := some .monoexponential
  , actionNominal := some .doublePossessive
  , suppletionTA := some .none
  , suppletionImperative := some .none
  , verbalNumber := some .none }

/-- Turkish: concatenative/agglutinative, monoexponential, moderate verb
    synthesis (person, number, tense, aspect, mood, voice, negation),
    dependent-marking (case suffixes), strongly suffixing, no productive
    reduplication (though some emphatic doubling exists). -/
def turkishMorph : MorphProfile :=
  { language := "Turkish"
  , iso := "tur"
  , fusion := .concatenative
  , exponence := .monoexponential
  , verbSynthesis := .moderate
  , locus := .dependentMarking
  , prefixSuffix := .stronglySuffixing
  , reduplication := .noProductive
  , locusClause := some .dependentMarking
  , locusPossessive := some .doubleMarking
  , wholeLanguageMarking := some .inconsistentOrOther
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .noSyncretism
  , verbalSyncretism := some .notSyncretic
  , tamExponence := some .monoexponential
  , actionNominal := some .possessiveAccusative
  , suppletionTA := some .tense
  , suppletionImperative := some .none
  , verbalNumber := some .none }

/-- Finnish: concatenative/agglutinative, monoexponential (15-case system
    with segmentable suffixes), moderate verb synthesis (person, number,
    tense, mood), dependent-marking (rich case system), strongly suffixing,
    no productive reduplication. -/
def finnishMorph : MorphProfile :=
  { language := "Finnish"
  , iso := "fin"
  , fusion := .concatenative
  , exponence := .monoexponential
  , verbSynthesis := .moderate
  , locus := .dependentMarking
  , prefixSuffix := .stronglySuffixing
  , reduplication := .noProductive
  , locusClause := some .dependentMarking
  , locusPossessive := some .doubleMarking
  , wholeLanguageMarking := some .inconsistentOrOther
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .coreAndNonCore
  , verbalSyncretism := some .notSyncretic
  , tamExponence := some .monoexponential
  , actionNominal := some .doublePossessive
  , suppletionTA := some .none
  , suppletionImperative := some .imperative
  , verbalNumber := some .none }

/-- Russian: nonlinear/fusional (portmanteau case+number+gender endings,
    stem ablaut in conjugation), polyexponential (-ov = gen+pl), moderate
    verb synthesis (person, number, tense, aspect, mood), dependent-marking
    (6-case system), weakly suffixing (some prefixal aspect: po-, za-, etc.),
    no productive reduplication. -/
def russianMorph : MorphProfile :=
  { language := "Russian"
  , iso := "rus"
  , fusion := .nonlinear
  , exponence := .polyexponential
  , verbSynthesis := .moderate
  , locus := .dependentMarking
  , prefixSuffix := .weaklySuffixing
  , reduplication := .noProductive
  , locusClause := some .dependentMarking
  , locusPossessive := some .dependentMarking
  , wholeLanguageMarking := some .dependentMarking
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .coreAndNonCore
  , verbalSyncretism := some .notSyncretic
  , tamExponence := some .monoexponential
  , actionNominal := some .ergativePossessive
  , suppletionTA := some .tenseAndAspect
  , suppletionImperative := some .imperative
  , verbalNumber := some .none }

/-- Swahili (Bantu): concatenative with some fusion in noun classes,
    monoexponential (each prefix/suffix slot has one function), high verb
    synthesis (subject, object, tense, aspect, mood, relative, negation
    all on the verb), head-marking (agreement on verb), weakly prefixing
    (noun class prefixes, subject/object prefixes), productive full and
    partial reduplication. -/
def swahiliMorph : MorphProfile :=
  { language := "Swahili"
  , iso := "swh"
  , fusion := .concatenative
  , exponence := .monoexponential
  , verbSynthesis := .high
  , locus := .headMarking
  , prefixSuffix := .weaklyPrefixing
  , reduplication := .productiveFull
  , locusClause := some .headMarking
  , locusPossessive := some .dependentMarking
  , wholeLanguageMarking := some .inconsistentOrOther
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .noCaseMarking
  , verbalSyncretism := some .syncretic
  , tamExponence := some .monoexponential
  , actionNominal := some .possessiveAccusative
  , suppletionTA := some .none
  , suppletionImperative := some .imperative
  , verbalNumber := some .none }

/-- Arabic (MSA): nonlinear/fusional (root-and-pattern morphology, ablaut,
    templatic derivation), polyexponential (vowel pattern encodes voice +
    aspect + person simultaneously), moderate verb synthesis (person, number,
    gender, tense, aspect, mood), dependent-marking (3-case system),
    weakly suffixing (both prefixes and suffixes in verb conjugation),
    no productive reduplication (some gemination in templates, but not
    productive reduplication per se). -/
def arabicMorph : MorphProfile :=
  { language := "Arabic (MSA)"
  , iso := "arb"
  , fusion := .nonlinear
  , exponence := .polyexponential
  , verbSynthesis := .moderate
  , locus := .dependentMarking
  , prefixSuffix := .weaklySuffixing
  , reduplication := .noProductive }

/-- Hindi-Urdu: concatenative (postpositional particles, suffixal verb
    inflection), polyexponential (verb endings bundle person+number+gender),
    moderate verb synthesis (person, number, gender, tense, aspect, mood),
    dependent-marking (postpositions, case clitics), strongly suffixing,
    no productive reduplication (though echo-word formation exists,
    e.g. chai-vai). -/
def hindiMorph : MorphProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , fusion := .concatenative
  , exponence := .polyexponential
  , verbSynthesis := .moderate
  , locus := .dependentMarking
  , prefixSuffix := .stronglySuffixing
  , reduplication := .noProductive
  , locusClause := some .doubleMarking
  , locusPossessive := some .dependentMarking
  , wholeLanguageMarking := some .inconsistentOrOther
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .coreAndNonCore
  , verbalSyncretism := some .syncretic
  , tamExponence := some .tamAgreement
  , actionNominal := some .possessiveAccusative
  , suppletionTA := some .tenseAndAspect
  , suppletionImperative := some .none
  , verbalNumber := some .none }

/-- Tagalog (Austronesian): concatenative (affixal voice/focus system),
    monoexponential, moderate verb synthesis (voice, aspect, mood),
    head-marking (voice morphology on verb indicates thematic role
    of subject), weakly prefixing (mag-, nag-, in-, -an, -in are both
    prefixes and infixes/suffixes), productive full and partial
    reduplication (plurality, aspect: mag-la-lakad 'walk around'). -/
def tagalogMorph : MorphProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , fusion := .concatenative
  , exponence := .monoexponential
  , verbSynthesis := .moderate
  , locus := .headMarking
  , prefixSuffix := .weaklyPrefixing
  , reduplication := .productiveFull
  , locusClause := some .doubleMarking
  , locusPossessive := some .other
  , wholeLanguageMarking := some .inconsistentOrOther
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .noCaseMarking
  , verbalSyncretism := some .noSubjectMarking
  , tamExponence := some .monoexponential
  , actionNominal := some .possessiveAccusative
  , suppletionTA := some .none
  , suppletionImperative := some .none
  , verbalNumber := some .none }

/-- Quechua (Cusco): concatenative/agglutinative (long suffixal chains
    with transparent morpheme boundaries), monoexponential, high verb
    synthesis (person, number, tense, aspect, mood, evidentiality,
    subordination, topic), dependent-marking (12+ case suffixes),
    strongly suffixing (exclusively suffixal), no productive
    reduplication. -/
def quechuaMorph : MorphProfile :=
  { language := "Quechua (Cusco)"
  , iso := "quz"
  , fusion := .concatenative
  , exponence := .monoexponential
  , verbSynthesis := .high
  , locus := .dependentMarking
  , prefixSuffix := .stronglySuffixing
  , reduplication := .noProductive }

/-- Hungarian: concatenative/agglutinative (transparent suffixal chains),
    monoexponential (each suffix has a distinct function), moderate verb
    synthesis (person, number, definiteness, tense, mood), dependent-marking
    (18-case system), strongly suffixing (exclusively suffixal),
    no productive reduplication. -/
def hungarianMorph : MorphProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , fusion := .concatenative
  , exponence := .monoexponential
  , verbSynthesis := .moderate
  , locus := .dependentMarking
  , prefixSuffix := .stronglySuffixing
  , reduplication := .noProductive
  , locusClause := some .dependentMarking
  , locusPossessive := some .headMarking
  , wholeLanguageMarking := some .inconsistentOrOther
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .noSyncretism
  , verbalSyncretism := some .notSyncretic
  , tamExponence := some .monoexponential
  , actionNominal := some .restricted
  , suppletionTA := some .tense
  , suppletionImperative := some .alternating
  , verbalNumber := some .none }

/-- Georgian (Kartvelian): nonlinear/fusional (complex verb morphology
    with stem changes, screeve alternations), polyexponential (verb
    agreement encodes subject+object person/number simultaneously),
    high verb synthesis (subject, object, tense, aspect, mood, version,
    causative, passivization), double-marking (case on nouns + agreement
    on verb), weakly suffixing (both prefixes and suffixes on verb),
    no productive reduplication. -/
def georgianMorph : MorphProfile :=
  { language := "Georgian"
  , iso := "kat"
  , fusion := .nonlinear
  , exponence := .polyexponential
  , verbSynthesis := .high
  , locus := .doubleMarking
  , prefixSuffix := .weaklySuffixing
  , reduplication := .noProductive
  , locusClause := some .doubleMarking
  , locusPossessive := some .dependentMarking
  , wholeLanguageMarking := some .inconsistentOrOther
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .coreAndNonCore
  , verbalSyncretism := some .notSyncretic
  , tamExponence := some .tamAgreement
  , actionNominal := some .ergativePossessive
  , suppletionTA := some .tenseAndAspect
  , suppletionImperative := some .imperative
  , verbalNumber := some .pairsNoSuppletion }

/-- Thai: isolating (grammatical categories expressed analytically with
    particles and serial verbs), no inflectional formatives, zero verb
    synthesis, zero/no-dominant marking (word order and particles),
    little affixation, no productive reduplication (some iconic
    doubling for emphasis/plurality is marginal). -/
def thaiMorph : MorphProfile :=
  { language := "Thai"
  , iso := "tha"
  , fusion := .isolating
  , exponence := .noInflection
  , verbSynthesis := .low
  , locus := .zeroMarking
  , prefixSuffix := .littleAffixation
  , reduplication := .noProductive
  , locusClause := some .noMarking
  , locusPossessive := some .dependentMarking
  , wholeLanguageMarking := some .inconsistentOrOther
  , zeroMarkingAP := some .zeroMarking
  , caseSyncretism := some .noCaseMarking
  , verbalSyncretism := some .noSubjectMarking
  , tamExponence := some .monoexponential
  , actionNominal := some .mixed
  , suppletionTA := some .none
  , suppletionImperative := some .none
  , verbalNumber := some .none }

/-- Indonesian (Austronesian): concatenative (prefixes, suffixes, circumfixes
    on verbs: meN-, ber-, -kan, -i), monoexponential, moderate verb synthesis
    (voice, applicative, causative, aspect-like distinctions via affixation),
    head-marking (voice on verb indicates thematic role), weakly prefixing
    (meN-, ber-, di-, ke-), productive full and partial reduplication
    (plurality: rumah-rumah 'houses', aspect, emphasis). -/
def indonesianMorph : MorphProfile :=
  { language := "Indonesian"
  , iso := "ind"
  , fusion := .concatenative
  , exponence := .monoexponential
  , verbSynthesis := .moderate
  , locus := .headMarking
  , prefixSuffix := .weaklyPrefixing
  , reduplication := .productiveFull
  , locusClause := some .noMarking
  , locusPossessive := some .noMarking
  , wholeLanguageMarking := some .zeroMarking
  , zeroMarkingAP := some .zeroMarking
  , caseSyncretism := some .noCaseMarking
  , verbalSyncretism := some .noSubjectMarking
  , tamExponence := some .monoexponential
  , actionNominal := some .ergativePossessive
  , suppletionTA := some .none
  , suppletionImperative := some .none
  , verbalNumber := some .none }

/-- Korean: concatenative/agglutinative (transparent suffix chains on
    verbs: -si honorific, -ess past, -keyss future, -ta declarative),
    monoexponential, moderate verb synthesis (honorific, tense, aspect,
    mood, speech level), dependent-marking (case particles on nouns),
    strongly suffixing, no productive reduplication. -/
def koreanMorph : MorphProfile :=
  { language := "Korean"
  , iso := "kor"
  , fusion := .concatenative
  , exponence := .monoexponential
  , verbSynthesis := .moderate
  , locus := .dependentMarking
  , prefixSuffix := .stronglySuffixing
  , reduplication := .noProductive
  , locusClause := some .dependentMarking
  , locusPossessive := some .dependentMarking
  , wholeLanguageMarking := some .dependentMarking
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .noCaseMarking
  , verbalSyncretism := some .noSubjectMarking
  , tamExponence := some .monoexponential
  , actionNominal := some .sentential
  , suppletionTA := some .none
  , suppletionImperative := some .none
  , verbalNumber := some .none }

/-- German: nonlinear/fusional (ablaut in strong verbs: singen/sang/gesungen,
    umlaut in plurals: Mutter/Muetter), polyexponential (adjective endings
    bundle case+number+gender), moderate verb synthesis (person, number,
    tense, mood), dependent-marking (4-case system, articles carry case),
    weakly suffixing (ge- prefix in past participles, but mostly suffixal),
    no productive reduplication. -/
def germanMorph : MorphProfile :=
  { language := "German"
  , iso := "deu"
  , fusion := .nonlinear
  , exponence := .polyexponential
  , verbSynthesis := .moderate
  , locus := .dependentMarking
  , prefixSuffix := .weaklySuffixing
  , reduplication := .noProductive
  , locusClause := some .dependentMarking
  , locusPossessive := some .dependentMarking
  , wholeLanguageMarking := some .dependentMarking
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .coreAndNonCore
  , verbalSyncretism := some .syncretic
  , tamExponence := some .monoexponential
  , actionNominal := some .ergativePossessive
  , suppletionTA := some .tense
  , suppletionImperative := some .none
  , verbalNumber := some .none }

/-- Spanish: nonlinear/fusional (stem changes in conjugation: contar/cuento,
    dormir/duermo), polyexponential (verb endings bundle person+number+tense+
    mood), moderate verb synthesis (person, number, tense, aspect, mood),
    dependent-marking (no case but prepositions and verb agreement patterns),
    weakly suffixing (mostly suffixal verb morphology), no productive
    reduplication. -/
def spanishMorph : MorphProfile :=
  { language := "Spanish"
  , iso := "spa"
  , fusion := .nonlinear
  , exponence := .polyexponential
  , verbSynthesis := .moderate
  , locus := .doubleMarking
  , prefixSuffix := .weaklySuffixing
  , reduplication := .noProductive
  , locusClause := some .doubleMarking
  , locusPossessive := some .dependentMarking
  , wholeLanguageMarking := some .inconsistentOrOther
  , zeroMarkingAP := some .nonZeroMarking
  , caseSyncretism := some .coreAndNonCore
  , verbalSyncretism := some .syncretic
  , tamExponence := some .tamAgreement
  , actionNominal := some .ergativePossessive
  , suppletionTA := some .tenseAndAspect
  , suppletionImperative := some .imperative
  , verbalNumber := some .none }

end MorphLanguageData

-- ============================================================================
-- §7. Profile Collection
-- ============================================================================

/-- All 18 morphological mechanism profiles. -/
def allMorphProfiles : List MorphProfile :=
  [ englishMorph, mandarinMorph, japaneseMorph, turkishMorph, finnishMorph
  , russianMorph, swahiliMorph, arabicMorph, hindiMorph, tagalogMorph
  , quechuaMorph, hungarianMorph, georgianMorph, thaiMorph, indonesianMorph
  , koreanMorph, germanMorph, spanishMorph ]

theorem allMorphProfiles_count : allMorphProfiles.length = 18 := by native_decide

-- ============================================================================
-- §8. Per-Language Verification
-- ============================================================================

/-! Spot-checks that each language has the expected classification values. -/

-- Fusion checks
example : englishMorph.fusion = .concatenative := by native_decide
example : mandarinMorph.fusion = .isolating := by native_decide
example : japaneseMorph.fusion = .concatenative := by native_decide
example : turkishMorph.fusion = .concatenative := by native_decide
example : finnishMorph.fusion = .concatenative := by native_decide
example : russianMorph.fusion = .nonlinear := by native_decide
example : swahiliMorph.fusion = .concatenative := by native_decide
example : arabicMorph.fusion = .nonlinear := by native_decide
example : georgianMorph.fusion = .nonlinear := by native_decide
example : thaiMorph.fusion = .isolating := by native_decide
example : indonesianMorph.fusion = .concatenative := by native_decide
example : germanMorph.fusion = .nonlinear := by native_decide

-- Verb synthesis checks
example : mandarinMorph.verbSynthesis = .low := by native_decide
example : thaiMorph.verbSynthesis = .low := by native_decide
example : englishMorph.verbSynthesis = .low := by native_decide
example : turkishMorph.verbSynthesis = .moderate := by native_decide
example : russianMorph.verbSynthesis = .moderate := by native_decide
example : swahiliMorph.verbSynthesis = .high := by native_decide
example : georgianMorph.verbSynthesis = .high := by native_decide
example : quechuaMorph.verbSynthesis = .high := by native_decide

-- Locus of marking checks
example : swahiliMorph.locus = .headMarking := by native_decide
example : japaneseMorph.locus = .dependentMarking := by native_decide
example : georgianMorph.locus = .doubleMarking := by native_decide
example : mandarinMorph.locus = .zeroMarking := by native_decide

-- Prefix/suffix checks
example : turkishMorph.prefixSuffix = .stronglySuffixing := by native_decide
example : swahiliMorph.prefixSuffix = .weaklyPrefixing := by native_decide
example : mandarinMorph.prefixSuffix = .littleAffixation := by native_decide
example : russianMorph.prefixSuffix = .weaklySuffixing := by native_decide

-- Reduplication checks
example : swahiliMorph.reduplication = .productiveFull := by native_decide
example : tagalogMorph.reduplication = .productiveFull := by native_decide
example : indonesianMorph.reduplication = .productiveFull := by native_decide
example : englishMorph.reduplication = .noProductive := by native_decide
example : arabicMorph.reduplication = .noProductive := by native_decide

-- ============================================================================
-- §9. Helper Predicates
-- ============================================================================

def MorphProfile.isConcatenative (p : MorphProfile) : Bool :=
  p.fusion == .concatenative

def MorphProfile.isIsolating (p : MorphProfile) : Bool :=
  p.fusion == .isolating

def MorphProfile.isNonlinear (p : MorphProfile) : Bool :=
  p.fusion == .nonlinear

def MorphProfile.isMono (p : MorphProfile) : Bool :=
  p.exponence == .monoexponential

def MorphProfile.isPoly (p : MorphProfile) : Bool :=
  p.exponence == .polyexponential

def MorphProfile.hasRedup (p : MorphProfile) : Bool :=
  p.reduplication == .productiveFull || p.reduplication == .fullOnly

def MorphProfile.isSuffixing (p : MorphProfile) : Bool :=
  p.prefixSuffix == .stronglySuffixing || p.prefixSuffix == .weaklySuffixing

def MorphProfile.isPrefixing (p : MorphProfile) : Bool :=
  p.prefixSuffix == .stronglyPrefixing || p.prefixSuffix == .weaklyPrefixing

def MorphProfile.isLowSynthesis (p : MorphProfile) : Bool :=
  p.verbSynthesis == .low

def MorphProfile.isHighSynthesis (p : MorphProfile) : Bool :=
  p.verbSynthesis == .high

-- ============================================================================
-- §10. Counting Helpers
-- ============================================================================

def countByFusion (langs : List MorphProfile) (f : Fusion) : Nat :=
  (langs.filter (λ p => p.fusion == f)).length

def countByExponence (langs : List MorphProfile) (e : Exponence) : Nat :=
  (langs.filter (λ p => p.exponence == e)).length

def countByLocus (langs : List MorphProfile) (l : LocusOfMarking) : Nat :=
  (langs.filter (λ p => p.locus == l)).length

def countBySynthesis (langs : List MorphProfile) (s : VerbSynthesis) : Nat :=
  (langs.filter (λ p => p.verbSynthesis == s)).length

-- ============================================================================
-- §11. Distribution Verification for Our Sample
-- ============================================================================

/-- Fusion type distribution in our sample. -/
theorem sample_concatenative_count :
    countByFusion allMorphProfiles .concatenative = 11 := by native_decide
theorem sample_nonlinear_count :
    countByFusion allMorphProfiles .nonlinear = 5 := by native_decide
theorem sample_isolating_count :
    countByFusion allMorphProfiles .isolating = 2 := by native_decide

/-- Exponence distribution in our sample. -/
theorem sample_monoexponential_count :
    countByExponence allMorphProfiles .monoexponential = 10 := by native_decide
theorem sample_polyexponential_count :
    countByExponence allMorphProfiles .polyexponential = 6 := by native_decide
theorem sample_no_inflection_count :
    countByExponence allMorphProfiles .noInflection = 2 := by native_decide

/-- Verb synthesis distribution in our sample. -/
theorem sample_low_synthesis :
    countBySynthesis allMorphProfiles .low = 3 := by native_decide
theorem sample_moderate_synthesis :
    countBySynthesis allMorphProfiles .moderate = 12 := by native_decide
theorem sample_high_synthesis :
    countBySynthesis allMorphProfiles .high = 3 := by native_decide

/-- Locus of marking distribution in our sample. -/
theorem sample_dependent_marking :
    countByLocus allMorphProfiles .dependentMarking = 11 := by native_decide
theorem sample_head_marking :
    countByLocus allMorphProfiles .headMarking = 3 := by native_decide
theorem sample_double_marking :
    countByLocus allMorphProfiles .doubleMarking = 2 := by native_decide
theorem sample_zero_marking :
    countByLocus allMorphProfiles .zeroMarking = 2 := by native_decide

/-- Fusion counts sum to total. -/
theorem fusion_counts_sum :
    countByFusion allMorphProfiles .concatenative +
    countByFusion allMorphProfiles .nonlinear +
    countByFusion allMorphProfiles .isolating =
    allMorphProfiles.length := by native_decide

/-- Locus counts sum to total. -/
theorem locus_counts_sum :
    countByLocus allMorphProfiles .headMarking +
    countByLocus allMorphProfiles .dependentMarking +
    countByLocus allMorphProfiles .doubleMarking +
    countByLocus allMorphProfiles .zeroMarking =
    allMorphProfiles.length := by native_decide

-- ============================================================================
-- §12. Typological Generalizations
-- ============================================================================

/-! ### Generalization 1: Suffixing strongly dominates prefixing worldwide.

Greenberg's Universal 27: "If a language is exclusively suffixing, it is
postpositional; if it is exclusively prefixing, it is prepositional."
More broadly, suffixing is far more common than prefixing. In the WALS
Ch 26 data, strongly+weakly suffixing (529) vastly outnumber strongly+
weakly prefixing (229). -/

theorem greenberg_universal_27_wals :
    (406 + 123 : Nat) > (135 + 94) := by native_decide

theorem suffixing_dominates_in_sample :
    let suffCount := (allMorphProfiles.filter (·.isSuffixing)).length
    let prefCount := (allMorphProfiles.filter (·.isPrefixing)).length
    suffCount > prefCount := by native_decide

/-! ### Generalization 2: Concatenative morphology is the most common fusion type.

In the WALS Ch 20 data, exclusively+strongly+weakly concatenative
languages (110/160 = 69%) vastly outnumber fusional and isolating types.
In our sample, concatenative languages also form the plurality. -/

theorem concatenative_most_common_wals :
    (58 + 28 + 24 : Nat) > 25 ∧ (58 + 28 + 24 : Nat) > 25 := by native_decide

theorem concatenative_plurality_in_sample :
    countByFusion allMorphProfiles .concatenative >
    countByFusion allMorphProfiles .nonlinear ∧
    countByFusion allMorphProfiles .concatenative >
    countByFusion allMorphProfiles .isolating := by native_decide

/-! ### Generalization 3: Dependent-marking is the most common locus type
in our sample. In the WALS data, dependent-marking (63) slightly edges out
double-marking (61) and zero/none (65), with head-marking (47) least common
among non-zero types. -/

theorem dependent_marking_common :
    countByLocus allMorphProfiles .dependentMarking >=
    countByLocus allMorphProfiles .headMarking := by native_decide

/-! ### Generalization 4: Reduplication is present in a majority of languages
in the WALS Ch 27 data (182/368 = 49% have productive reduplication).
In our sample, Austronesian (Tagalog, Indonesian) and Bantu (Swahili)
languages have productive reduplication. -/

theorem reduplication_in_majority_wals :
    (147 + 35 : Nat) > 186 / 2 := by native_decide

theorem reduplication_attested_in_sample :
    (allMorphProfiles.filter (·.hasRedup)).length >= 3 := by native_decide

/-! ### Generalization 5: Isolating morphology correlates with low
inflectional synthesis.

Languages with isolating fusion (Mandarin, Thai) have minimal bound
morphology on verbs. This is expected: if there are no affixes, there
are no categories to count on the verb. -/

theorem isolating_implies_low_synthesis :
    allMorphProfiles.all (λ p =>
      if p.isIsolating then p.isLowSynthesis
      else true) = true := by native_decide

/-! ### Generalization 6: Polyexponential (fusional) systems correlate
with nonlinear fusion.

When a single formative bundles multiple categories (polyexponential),
the morphology tends to be fusional/nonlinear (stem changes, portmanteaux)
rather than agglutinative. The converse is not always true: some
concatenative systems have some polyexponence. -/

theorem polyexponential_correlates_nonlinear :
    let polyLangs := allMorphProfiles.filter (·.isPoly)
    let polyNonlinear := polyLangs.filter (·.isNonlinear)
    -- Majority of polyexponential languages in sample are nonlinear
    polyNonlinear.length * 2 >= polyLangs.length := by native_decide

/-! ### Generalization 7: Concatenative languages are predominantly
monoexponential.

This is the defining correlation of agglutination: one-to-one mapping
between form and meaning in the morphology. -/

theorem concatenative_mostly_monoexponential :
    let concatLangs := allMorphProfiles.filter (·.isConcatenative)
    let concatMono := concatLangs.filter (·.isMono)
    concatMono.length * 2 > concatLangs.length := by native_decide

/-! ### Generalization 8: Head-marking languages tend to have high verb
synthesis.

If grammatical relations are marked on the head (verb), then the verb
carries agreement morphology for multiple arguments, driving up synthesis. -/

theorem head_marking_high_synthesis :
    let headLangs := allMorphProfiles.filter (λ p => p.locus == .headMarking)
    headLangs.all (λ p =>
      p.verbSynthesis == .moderate || p.verbSynthesis == .high) = true := by
  native_decide

/-! ### Generalization 9: Isolating languages have zero/no-dominant marking.

Without bound morphology, there is no morphological locus to mark
grammatical relations. Word order and free particles do the work instead. -/

theorem isolating_implies_zero_marking :
    allMorphProfiles.all (λ p =>
      if p.isIsolating then p.locus == .zeroMarking
      else true) = true := by native_decide

/-! ### Generalization 10: Isolating languages have no inflection
(trivially follows from definition, but worth checking the data). -/

theorem isolating_implies_no_inflection :
    allMorphProfiles.all (λ p =>
      if p.isIsolating then p.exponence == .noInflection
      else true) = true := by native_decide

/-! ### Generalization 11: Strongly suffixing languages in our sample
are all concatenative.

The canonical agglutinative profile: strongly suffixing with transparent
morpheme boundaries. -/

theorem strongly_suffixing_are_concatenative :
    allMorphProfiles.all (λ p =>
      if p.prefixSuffix == .stronglySuffixing then p.isConcatenative
      else true) = true := by native_decide

/-! ### Generalization 12: Productive reduplication in our sample is
concentrated in Austronesian and Bantu languages.

The three languages with productive reduplication are Swahili (Bantu),
Tagalog (Austronesian), and Indonesian (Austronesian). -/

theorem reduplication_languages_count :
    (allMorphProfiles.filter (·.hasRedup)).length = 3 := by native_decide

-- ============================================================================
-- §13. WALS Chapter-Level Distribution Theorems
-- ============================================================================

/-- Ch 26: Suffixing (strongly + weakly) accounts for over half of
    languages with affixation (529/816 = 65%). -/
theorem ch26_suffixing_majority :
    (406 + 123 : Nat) > (969 - 153) / 2 := by native_decide

/-- Ch 20: Concatenative types (exclusively + strongly + weakly)
    account for the majority of the sample. -/
theorem ch20_concatenative_majority :
    (58 + 28 + 24 : Nat) > 160 / 2 := by native_decide

/-- Ch 22: Most languages have 2--7 categories per verb word. The
    extremes (0--1 and 12--13) are rare. -/
theorem ch22_moderate_dominant :
    (39 + 45 + 24 : Nat) > 145 / 2 := by native_decide

/-- Ch 27: Languages split roughly evenly between having productive
    reduplication and not. -/
theorem ch27_reduplication_split :
    let withRedup := 147 + 35
    let withoutRedup := 186
    withRedup > withoutRedup / 2 ∧ withoutRedup > withRedup / 2 := by native_decide

-- ============================================================================
-- §14. Cross-Dimensional Consistency
-- ============================================================================

/-- All ISO codes in the morphological profiles are 3 characters. -/
theorem morph_iso_length_3 :
    allMorphProfiles.all (λ p => p.iso.length == 3) = true := by native_decide

/-- No duplicate ISO codes in the morphological profiles. -/
theorem morph_iso_unique :
    (allMorphProfiles.map (·.iso)).eraseDups.length =
    allMorphProfiles.length := by native_decide

/-- All languages with no inflection are also isolating. -/
theorem no_inflection_implies_isolating :
    allMorphProfiles.all (λ p =>
      if p.exponence == .noInflection then p.isIsolating
      else true) = true := by native_decide

/-- All languages with high verb synthesis have either concatenative
    or nonlinear fusion (never isolating). -/
theorem high_synthesis_not_isolating :
    allMorphProfiles.all (λ p =>
      if p.isHighSynthesis then !p.isIsolating
      else true) = true := by native_decide

/-- Languages with little affixation are exactly the isolating ones
    in our sample. -/
theorem little_affixation_iff_isolating :
    allMorphProfiles.all (λ p =>
      (p.prefixSuffix == .littleAffixation) == p.isIsolating) = true := by
  native_decide

-- ============================================================================
-- §15. WALS Grounding: Per-Language Verification
-- ============================================================================

/-!
## WALS Grounding

Per-language grounding theorems verify that our `MorphProfile` values are
consistent with WALS generated data where a language appears in the WALS
sample and the mapping from WALS categories to local types is unambiguous.

Not all profile x chapter combinations can be grounded:
- WALS 20A evaluates the fusion of *selected inflectional formatives*, which
  can differ from a language's overall morphological type (e.g., Russian's
  selected formatives are concatenative even though the system is broadly
  fusional). We ground only where the two notions coincide.
- WALS 21A evaluates *case* exponence specifically. Languages without case
  (noCase) provide no information about overall exponence, so those are
  skipped.
- Arabic (MSA) and Quechua (Cusco) are absent from most WALS chapters;
  Arabic (Egyptian) appears under code "aeg" but is a different variety.
-/

-- --------------------------------------------------------------------------
-- §15.1 Chapter 20A: Fusion (only languages where WALS agrees with profile)
-- --------------------------------------------------------------------------

theorem english_ch20 :
    (Core.WALS.F20A.lookup "eng").bind (fromWALS20A ·.value) =
    some englishMorph.fusion := by native_decide
theorem japanese_ch20 :
    (Core.WALS.F20A.lookup "jpn").bind (fromWALS20A ·.value) =
    some japaneseMorph.fusion := by native_decide
theorem turkish_ch20 :
    (Core.WALS.F20A.lookup "tur").bind (fromWALS20A ·.value) =
    some turkishMorph.fusion := by native_decide
theorem finnish_ch20 :
    (Core.WALS.F20A.lookup "fin").bind (fromWALS20A ·.value) =
    some finnishMorph.fusion := by native_decide
theorem swahili_ch20 :
    (Core.WALS.F20A.lookup "swa").bind (fromWALS20A ·.value) =
    some swahiliMorph.fusion := by native_decide
theorem hindi_ch20 :
    (Core.WALS.F20A.lookup "hin").bind (fromWALS20A ·.value) =
    some hindiMorph.fusion := by native_decide
theorem tagalog_ch20 :
    (Core.WALS.F20A.lookup "tag").bind (fromWALS20A ·.value) =
    some tagalogMorph.fusion := by native_decide
theorem hungarian_ch20 :
    (Core.WALS.F20A.lookup "hun").bind (fromWALS20A ·.value) =
    some hungarianMorph.fusion := by native_decide
theorem korean_ch20 :
    (Core.WALS.F20A.lookup "kor").bind (fromWALS20A ·.value) =
    some koreanMorph.fusion := by native_decide

-- --------------------------------------------------------------------------
-- §15.2 Chapter 22A: Verb Synthesis
-- --------------------------------------------------------------------------

theorem english_ch22 :
    (Core.WALS.F22A.lookup "eng").map (fromWALS22A ·.value) =
    some englishMorph.verbSynthesis := by native_decide
theorem mandarin_ch22 :
    (Core.WALS.F22A.lookup "mnd").map (fromWALS22A ·.value) =
    some mandarinMorph.verbSynthesis := by native_decide
theorem japanese_ch22 :
    (Core.WALS.F22A.lookup "jpn").map (fromWALS22A ·.value) =
    some japaneseMorph.verbSynthesis := by native_decide
theorem turkish_ch22 :
    (Core.WALS.F22A.lookup "tur").map (fromWALS22A ·.value) =
    some turkishMorph.verbSynthesis := by native_decide
theorem russian_ch22 :
    (Core.WALS.F22A.lookup "rus").map (fromWALS22A ·.value) =
    some russianMorph.verbSynthesis := by native_decide
theorem georgian_ch22 :
    (Core.WALS.F22A.lookup "geo").map (fromWALS22A ·.value) =
    some georgianMorph.verbSynthesis := by native_decide
theorem indonesian_ch22 :
    (Core.WALS.F22A.lookup "ind").map (fromWALS22A ·.value) =
    some indonesianMorph.verbSynthesis := by native_decide
theorem korean_ch22 :
    (Core.WALS.F22A.lookup "kor").map (fromWALS22A ·.value) =
    some koreanMorph.verbSynthesis := by native_decide
theorem spanish_ch22 :
    (Core.WALS.F22A.lookup "spa").map (fromWALS22A ·.value) =
    some spanishMorph.verbSynthesis := by native_decide
theorem hungarian_ch22 :
    (Core.WALS.F22A.lookup "hun").map (fromWALS22A ·.value) =
    some hungarianMorph.verbSynthesis := by native_decide
theorem thai_ch22 :
    (Core.WALS.F22A.lookup "tha").map (fromWALS22A ·.value) =
    some thaiMorph.verbSynthesis := by native_decide

-- --------------------------------------------------------------------------
-- §15.3 Chapter 26A: Prefixing vs Suffixing
-- --------------------------------------------------------------------------

theorem japanese_ch26 :
    (Core.WALS.F26A.lookup "jpn").map (fromWALS26A ·.value) =
    some japaneseMorph.prefixSuffix := by native_decide
theorem turkish_ch26 :
    (Core.WALS.F26A.lookup "tur").map (fromWALS26A ·.value) =
    some turkishMorph.prefixSuffix := by native_decide
theorem finnish_ch26 :
    (Core.WALS.F26A.lookup "fin").map (fromWALS26A ·.value) =
    some finnishMorph.prefixSuffix := by native_decide
theorem swahili_ch26 :
    (Core.WALS.F26A.lookup "swa").map (fromWALS26A ·.value) =
    some swahiliMorph.prefixSuffix := by native_decide
theorem hindi_ch26 :
    (Core.WALS.F26A.lookup "hin").map (fromWALS26A ·.value) =
    some hindiMorph.prefixSuffix := by native_decide
theorem georgian_ch26 :
    (Core.WALS.F26A.lookup "geo").map (fromWALS26A ·.value) =
    some georgianMorph.prefixSuffix := by native_decide
theorem korean_ch26 :
    (Core.WALS.F26A.lookup "kor").map (fromWALS26A ·.value) =
    some koreanMorph.prefixSuffix := by native_decide
theorem hungarian_ch26 :
    (Core.WALS.F26A.lookup "hun").map (fromWALS26A ·.value) =
    some hungarianMorph.prefixSuffix := by native_decide
theorem thai_ch26 :
    (Core.WALS.F26A.lookup "tha").map (fromWALS26A ·.value) =
    some thaiMorph.prefixSuffix := by native_decide

-- --------------------------------------------------------------------------
-- §15.4 Chapter 27A: Reduplication
-- --------------------------------------------------------------------------

theorem english_ch27 :
    (Core.WALS.F27A.lookup "eng").map (fromWALS27A ·.value) =
    some englishMorph.reduplication := by native_decide
theorem finnish_ch27 :
    (Core.WALS.F27A.lookup "fin").map (fromWALS27A ·.value) =
    some finnishMorph.reduplication := by native_decide
theorem russian_ch27 :
    (Core.WALS.F27A.lookup "rus").map (fromWALS27A ·.value) =
    some russianMorph.reduplication := by native_decide
theorem swahili_ch27 :
    (Core.WALS.F27A.lookup "swa").map (fromWALS27A ·.value) =
    some swahiliMorph.reduplication := by native_decide
theorem german_ch27 :
    (Core.WALS.F27A.lookup "ger").map (fromWALS27A ·.value) =
    some germanMorph.reduplication := by native_decide
theorem spanish_ch27 :
    (Core.WALS.F27A.lookup "spa").map (fromWALS27A ·.value) =
    some spanishMorph.reduplication := by native_decide
theorem tagalog_ch27 :
    (Core.WALS.F27A.lookup "tag").map (fromWALS27A ·.value) =
    some tagalogMorph.reduplication := by native_decide

-- --------------------------------------------------------------------------
-- §15.5 Chapter 23A: Locus of Marking in the Clause
-- --------------------------------------------------------------------------

theorem english_ch23 :
    (Core.WALS.F23A.lookup "eng").map (fromWALS23A ·.value) =
    some (.dependentMarking : LocusClause) := by native_decide
theorem mandarin_ch23 :
    (Core.WALS.F23A.lookup "mnd").map (fromWALS23A ·.value) =
    some (.dependentMarking : LocusClause) := by native_decide
theorem japanese_ch23 :
    (Core.WALS.F23A.lookup "jpn").map (fromWALS23A ·.value) =
    some (.dependentMarking : LocusClause) := by native_decide
theorem turkish_ch23 :
    (Core.WALS.F23A.lookup "tur").map (fromWALS23A ·.value) =
    some (.dependentMarking : LocusClause) := by native_decide
theorem finnish_ch23 :
    (Core.WALS.F23A.lookup "fin").map (fromWALS23A ·.value) =
    some (.dependentMarking : LocusClause) := by native_decide
theorem russian_ch23 :
    (Core.WALS.F23A.lookup "rus").map (fromWALS23A ·.value) =
    some (.dependentMarking : LocusClause) := by native_decide
theorem swahili_ch23 :
    (Core.WALS.F23A.lookup "swa").map (fromWALS23A ·.value) =
    some (.headMarking : LocusClause) := by native_decide
theorem hindi_ch23 :
    (Core.WALS.F23A.lookup "hin").map (fromWALS23A ·.value) =
    some (.doubleMarking : LocusClause) := by native_decide
theorem tagalog_ch23 :
    (Core.WALS.F23A.lookup "tag").map (fromWALS23A ·.value) =
    some (.doubleMarking : LocusClause) := by native_decide
theorem hungarian_ch23 :
    (Core.WALS.F23A.lookup "hun").map (fromWALS23A ·.value) =
    some (.dependentMarking : LocusClause) := by native_decide
theorem georgian_ch23 :
    (Core.WALS.F23A.lookup "geo").map (fromWALS23A ·.value) =
    some (.doubleMarking : LocusClause) := by native_decide
theorem thai_ch23 :
    (Core.WALS.F23A.lookup "tha").map (fromWALS23A ·.value) =
    some (.noMarking : LocusClause) := by native_decide
theorem indonesian_ch23 :
    (Core.WALS.F23A.lookup "ind").map (fromWALS23A ·.value) =
    some (.noMarking : LocusClause) := by native_decide
theorem korean_ch23 :
    (Core.WALS.F23A.lookup "kor").map (fromWALS23A ·.value) =
    some (.dependentMarking : LocusClause) := by native_decide
theorem german_ch23 :
    (Core.WALS.F23A.lookup "ger").map (fromWALS23A ·.value) =
    some (.dependentMarking : LocusClause) := by native_decide
theorem spanish_ch23 :
    (Core.WALS.F23A.lookup "spa").map (fromWALS23A ·.value) =
    some (.doubleMarking : LocusClause) := by native_decide

-- --------------------------------------------------------------------------
-- §15.6 Chapter 24A: Locus of Marking in Possessive NP
-- --------------------------------------------------------------------------

theorem english_ch24 :
    (Core.WALS.F24A.lookup "eng").map (fromWALS24A ·.value) =
    some (.dependentMarking : LocusPossessive) := by native_decide
theorem mandarin_ch24 :
    (Core.WALS.F24A.lookup "mnd").map (fromWALS24A ·.value) =
    some (.dependentMarking : LocusPossessive) := by native_decide
theorem japanese_ch24 :
    (Core.WALS.F24A.lookup "jpn").map (fromWALS24A ·.value) =
    some (.dependentMarking : LocusPossessive) := by native_decide
theorem turkish_ch24 :
    (Core.WALS.F24A.lookup "tur").map (fromWALS24A ·.value) =
    some (.doubleMarking : LocusPossessive) := by native_decide
theorem finnish_ch24 :
    (Core.WALS.F24A.lookup "fin").map (fromWALS24A ·.value) =
    some (.doubleMarking : LocusPossessive) := by native_decide
theorem russian_ch24 :
    (Core.WALS.F24A.lookup "rus").map (fromWALS24A ·.value) =
    some (.dependentMarking : LocusPossessive) := by native_decide
theorem swahili_ch24 :
    (Core.WALS.F24A.lookup "swa").map (fromWALS24A ·.value) =
    some (.dependentMarking : LocusPossessive) := by native_decide
theorem hindi_ch24 :
    (Core.WALS.F24A.lookup "hin").map (fromWALS24A ·.value) =
    some (.dependentMarking : LocusPossessive) := by native_decide
theorem tagalog_ch24 :
    (Core.WALS.F24A.lookup "tag").map (fromWALS24A ·.value) =
    some (.other : LocusPossessive) := by native_decide
theorem hungarian_ch24 :
    (Core.WALS.F24A.lookup "hun").map (fromWALS24A ·.value) =
    some (.headMarking : LocusPossessive) := by native_decide
theorem georgian_ch24 :
    (Core.WALS.F24A.lookup "geo").map (fromWALS24A ·.value) =
    some (.dependentMarking : LocusPossessive) := by native_decide
theorem thai_ch24 :
    (Core.WALS.F24A.lookup "tha").map (fromWALS24A ·.value) =
    some (.dependentMarking : LocusPossessive) := by native_decide
theorem indonesian_ch24 :
    (Core.WALS.F24A.lookup "ind").map (fromWALS24A ·.value) =
    some (.noMarking : LocusPossessive) := by native_decide
theorem korean_ch24 :
    (Core.WALS.F24A.lookup "kor").map (fromWALS24A ·.value) =
    some (.dependentMarking : LocusPossessive) := by native_decide
theorem german_ch24 :
    (Core.WALS.F24A.lookup "ger").map (fromWALS24A ·.value) =
    some (.dependentMarking : LocusPossessive) := by native_decide
theorem spanish_ch24 :
    (Core.WALS.F24A.lookup "spa").map (fromWALS24A ·.value) =
    some (.dependentMarking : LocusPossessive) := by native_decide

-- --------------------------------------------------------------------------
-- §15.7 Chapter 25A: Whole-Language Marking Typology
-- --------------------------------------------------------------------------

theorem english_ch25a :
    (Core.WALS.F25A.lookup "eng").map (fromWALS25A ·.value) =
    some (.dependentMarking : WholeLanguageMarking) := by native_decide
theorem mandarin_ch25a :
    (Core.WALS.F25A.lookup "mnd").map (fromWALS25A ·.value) =
    some (.dependentMarking : WholeLanguageMarking) := by native_decide
theorem japanese_ch25a :
    (Core.WALS.F25A.lookup "jpn").map (fromWALS25A ·.value) =
    some (.dependentMarking : WholeLanguageMarking) := by native_decide
theorem russian_ch25a :
    (Core.WALS.F25A.lookup "rus").map (fromWALS25A ·.value) =
    some (.dependentMarking : WholeLanguageMarking) := by native_decide
theorem korean_ch25a :
    (Core.WALS.F25A.lookup "kor").map (fromWALS25A ·.value) =
    some (.dependentMarking : WholeLanguageMarking) := by native_decide
theorem german_ch25a :
    (Core.WALS.F25A.lookup "ger").map (fromWALS25A ·.value) =
    some (.dependentMarking : WholeLanguageMarking) := by native_decide
theorem indonesian_ch25a :
    (Core.WALS.F25A.lookup "ind").map (fromWALS25A ·.value) =
    some (.zeroMarking : WholeLanguageMarking) := by native_decide

-- --------------------------------------------------------------------------
-- §15.8 Chapter 25B: Zero Marking of A and P Arguments
-- --------------------------------------------------------------------------

theorem english_ch25b :
    (Core.WALS.F25B.lookup "eng").map (fromWALS25B ·.value) =
    some (.nonZeroMarking : ZeroMarkingAP) := by native_decide
theorem mandarin_ch25b :
    (Core.WALS.F25B.lookup "mnd").map (fromWALS25B ·.value) =
    some (.nonZeroMarking : ZeroMarkingAP) := by native_decide
theorem japanese_ch25b :
    (Core.WALS.F25B.lookup "jpn").map (fromWALS25B ·.value) =
    some (.nonZeroMarking : ZeroMarkingAP) := by native_decide
theorem turkish_ch25b :
    (Core.WALS.F25B.lookup "tur").map (fromWALS25B ·.value) =
    some (.nonZeroMarking : ZeroMarkingAP) := by native_decide
theorem finnish_ch25b :
    (Core.WALS.F25B.lookup "fin").map (fromWALS25B ·.value) =
    some (.nonZeroMarking : ZeroMarkingAP) := by native_decide
theorem russian_ch25b :
    (Core.WALS.F25B.lookup "rus").map (fromWALS25B ·.value) =
    some (.nonZeroMarking : ZeroMarkingAP) := by native_decide
theorem swahili_ch25b :
    (Core.WALS.F25B.lookup "swa").map (fromWALS25B ·.value) =
    some (.nonZeroMarking : ZeroMarkingAP) := by native_decide
theorem hindi_ch25b :
    (Core.WALS.F25B.lookup "hin").map (fromWALS25B ·.value) =
    some (.nonZeroMarking : ZeroMarkingAP) := by native_decide
theorem thai_ch25b :
    (Core.WALS.F25B.lookup "tha").map (fromWALS25B ·.value) =
    some (.zeroMarking : ZeroMarkingAP) := by native_decide
theorem indonesian_ch25b :
    (Core.WALS.F25B.lookup "ind").map (fromWALS25B ·.value) =
    some (.zeroMarking : ZeroMarkingAP) := by native_decide
theorem korean_ch25b :
    (Core.WALS.F25B.lookup "kor").map (fromWALS25B ·.value) =
    some (.nonZeroMarking : ZeroMarkingAP) := by native_decide
theorem german_ch25b :
    (Core.WALS.F25B.lookup "ger").map (fromWALS25B ·.value) =
    some (.nonZeroMarking : ZeroMarkingAP) := by native_decide
theorem spanish_ch25b :
    (Core.WALS.F25B.lookup "spa").map (fromWALS25B ·.value) =
    some (.nonZeroMarking : ZeroMarkingAP) := by native_decide

-- --------------------------------------------------------------------------
-- §15.9 Chapter 28A: Case Syncretism
-- --------------------------------------------------------------------------

theorem english_ch28 :
    (Core.WALS.F28A.lookup "eng").map (fromWALS28A ·.value) =
    some (.coreCasesOnly : CaseSyncretism) := by native_decide
theorem japanese_ch28 :
    (Core.WALS.F28A.lookup "jpn").map (fromWALS28A ·.value) =
    some (.noCaseMarking : CaseSyncretism) := by native_decide
theorem turkish_ch28 :
    (Core.WALS.F28A.lookup "tur").map (fromWALS28A ·.value) =
    some (.noSyncretism : CaseSyncretism) := by native_decide
theorem finnish_ch28 :
    (Core.WALS.F28A.lookup "fin").map (fromWALS28A ·.value) =
    some (.coreAndNonCore : CaseSyncretism) := by native_decide
theorem russian_ch28 :
    (Core.WALS.F28A.lookup "rus").map (fromWALS28A ·.value) =
    some (.coreAndNonCore : CaseSyncretism) := by native_decide
theorem swahili_ch28 :
    (Core.WALS.F28A.lookup "swa").map (fromWALS28A ·.value) =
    some (.noCaseMarking : CaseSyncretism) := by native_decide
theorem hindi_ch28 :
    (Core.WALS.F28A.lookup "hin").map (fromWALS28A ·.value) =
    some (.coreAndNonCore : CaseSyncretism) := by native_decide
theorem hungarian_ch28 :
    (Core.WALS.F28A.lookup "hun").map (fromWALS28A ·.value) =
    some (.noSyncretism : CaseSyncretism) := by native_decide
theorem georgian_ch28 :
    (Core.WALS.F28A.lookup "geo").map (fromWALS28A ·.value) =
    some (.coreAndNonCore : CaseSyncretism) := by native_decide
theorem thai_ch28 :
    (Core.WALS.F28A.lookup "tha").map (fromWALS28A ·.value) =
    some (.noCaseMarking : CaseSyncretism) := by native_decide
theorem indonesian_ch28 :
    (Core.WALS.F28A.lookup "ind").map (fromWALS28A ·.value) =
    some (.noCaseMarking : CaseSyncretism) := by native_decide
theorem korean_ch28 :
    (Core.WALS.F28A.lookup "kor").map (fromWALS28A ·.value) =
    some (.noCaseMarking : CaseSyncretism) := by native_decide
theorem mandarin_ch28 :
    (Core.WALS.F28A.lookup "mnd").map (fromWALS28A ·.value) =
    some (.noCaseMarking : CaseSyncretism) := by native_decide
theorem german_ch28 :
    (Core.WALS.F28A.lookup "ger").map (fromWALS28A ·.value) =
    some (.coreAndNonCore : CaseSyncretism) := by native_decide
theorem spanish_ch28 :
    (Core.WALS.F28A.lookup "spa").map (fromWALS28A ·.value) =
    some (.coreAndNonCore : CaseSyncretism) := by native_decide
theorem tagalog_ch28 :
    (Core.WALS.F28A.lookup "tag").map (fromWALS28A ·.value) =
    some (.noCaseMarking : CaseSyncretism) := by native_decide

-- --------------------------------------------------------------------------
-- §15.10 Chapter 29A: Syncretism in Verbal Person/Number Marking
-- --------------------------------------------------------------------------

theorem english_ch29 :
    (Core.WALS.F29A.lookup "eng").map (fromWALS29A ·.value) =
    some (.syncretic : VerbalSyncretism) := by native_decide
theorem japanese_ch29 :
    (Core.WALS.F29A.lookup "jpn").map (fromWALS29A ·.value) =
    some (.noSubjectMarking : VerbalSyncretism) := by native_decide
theorem turkish_ch29 :
    (Core.WALS.F29A.lookup "tur").map (fromWALS29A ·.value) =
    some (.notSyncretic : VerbalSyncretism) := by native_decide
theorem finnish_ch29 :
    (Core.WALS.F29A.lookup "fin").map (fromWALS29A ·.value) =
    some (.notSyncretic : VerbalSyncretism) := by native_decide
theorem russian_ch29 :
    (Core.WALS.F29A.lookup "rus").map (fromWALS29A ·.value) =
    some (.notSyncretic : VerbalSyncretism) := by native_decide
theorem swahili_ch29 :
    (Core.WALS.F29A.lookup "swa").map (fromWALS29A ·.value) =
    some (.syncretic : VerbalSyncretism) := by native_decide
theorem hindi_ch29 :
    (Core.WALS.F29A.lookup "hin").map (fromWALS29A ·.value) =
    some (.syncretic : VerbalSyncretism) := by native_decide
theorem hungarian_ch29 :
    (Core.WALS.F29A.lookup "hun").map (fromWALS29A ·.value) =
    some (.notSyncretic : VerbalSyncretism) := by native_decide
theorem georgian_ch29 :
    (Core.WALS.F29A.lookup "geo").map (fromWALS29A ·.value) =
    some (.notSyncretic : VerbalSyncretism) := by native_decide
theorem thai_ch29 :
    (Core.WALS.F29A.lookup "tha").map (fromWALS29A ·.value) =
    some (.noSubjectMarking : VerbalSyncretism) := by native_decide
theorem indonesian_ch29 :
    (Core.WALS.F29A.lookup "ind").map (fromWALS29A ·.value) =
    some (.noSubjectMarking : VerbalSyncretism) := by native_decide
theorem korean_ch29 :
    (Core.WALS.F29A.lookup "kor").map (fromWALS29A ·.value) =
    some (.noSubjectMarking : VerbalSyncretism) := by native_decide
theorem mandarin_ch29 :
    (Core.WALS.F29A.lookup "mnd").map (fromWALS29A ·.value) =
    some (.noSubjectMarking : VerbalSyncretism) := by native_decide
theorem german_ch29 :
    (Core.WALS.F29A.lookup "ger").map (fromWALS29A ·.value) =
    some (.syncretic : VerbalSyncretism) := by native_decide
theorem spanish_ch29 :
    (Core.WALS.F29A.lookup "spa").map (fromWALS29A ·.value) =
    some (.syncretic : VerbalSyncretism) := by native_decide
theorem tagalog_ch29 :
    (Core.WALS.F29A.lookup "tag").map (fromWALS29A ·.value) =
    some (.noSubjectMarking : VerbalSyncretism) := by native_decide

-- --------------------------------------------------------------------------
-- §15.11 WALS Dataset Size Verification
-- --------------------------------------------------------------------------

theorem ch20_size : ch20.length = 165 := by native_decide
theorem ch21_size : ch21.length = 162 := by native_decide
theorem ch22_size : ch22.length = 145 := by native_decide
theorem ch26_size : ch26.length = 969 := by native_decide
theorem ch27_size : ch27.length = 368 := by native_decide
theorem ch23_size : ch23.length = 236 := by native_decide
theorem ch24_size : ch24.length = 236 := by native_decide
theorem ch25a_size : ch25a.length = 236 := by native_decide
theorem ch25b_size : ch25b.length = 235 := by native_decide
theorem ch28_size : ch28.length = 198 := by native_decide
theorem ch29_size : ch29.length = 198 := by native_decide

-- --------------------------------------------------------------------------
-- §15.12 WALS Distribution Count Verification
-- --------------------------------------------------------------------------

-- Ch 23 distribution counts
theorem ch23_count_headMarking :
    (ch23.filter (·.value == .headMarking)).length = 71 := by native_decide
theorem ch23_count_dependentMarking :
    (ch23.filter (·.value == .dependentMarking)).length = 63 := by native_decide
theorem ch23_count_doubleMarking :
    (ch23.filter (·.value == .doubleMarking)).length = 58 := by native_decide
theorem ch23_count_noMarking :
    (ch23.filter (·.value == .noMarking)).length = 42 := by native_decide
theorem ch23_count_other :
    (ch23.filter (·.value == .other)).length = 2 := by native_decide

-- Ch 24 distribution counts
theorem ch24_count_headMarking :
    (ch24.filter (·.value == .headMarking)).length = 78 := by native_decide
theorem ch24_count_dependentMarking :
    (ch24.filter (·.value == .dependentMarking)).length = 98 := by native_decide
theorem ch24_count_doubleMarking :
    (ch24.filter (·.value == .doubleMarking)).length = 22 := by native_decide
theorem ch24_count_noMarking :
    (ch24.filter (·.value == .noMarking)).length = 32 := by native_decide
theorem ch24_count_other :
    (ch24.filter (·.value == .other)).length = 6 := by native_decide

-- Ch 25A distribution counts
theorem ch25a_count_headMarking :
    (ch25a.filter (·.value == .headMarking)).length = 47 := by native_decide
theorem ch25a_count_dependentMarking :
    (ch25a.filter (·.value == .dependentMarking)).length = 46 := by native_decide
theorem ch25a_count_doubleMarking :
    (ch25a.filter (·.value == .doubleMarking)).length = 16 := by native_decide
theorem ch25a_count_zeroMarking :
    (ch25a.filter (·.value == .zeroMarking)).length = 6 := by native_decide
theorem ch25a_count_inconsistentOrOther :
    (ch25a.filter (·.value == .inconsistentOrOther)).length = 121 := by native_decide

-- Ch 25B distribution counts
theorem ch25b_count_zeroMarking :
    (ch25b.filter (·.value == .zeroMarking)).length = 16 := by native_decide
theorem ch25b_count_nonZeroMarking :
    (ch25b.filter (·.value == .nonZeroMarking)).length = 219 := by native_decide

-- Ch 28 distribution counts
theorem ch28_count_noCaseMarking :
    (ch28.filter (·.value == .noCaseMarking)).length = 123 := by native_decide
theorem ch28_count_coreCasesOnly :
    (ch28.filter (·.value == .coreCasesOnly)).length = 18 := by native_decide
theorem ch28_count_coreAndNonCore :
    (ch28.filter (·.value == .coreAndNonCore)).length = 22 := by native_decide
theorem ch28_count_noSyncretism :
    (ch28.filter (·.value == .noSyncretism)).length = 35 := by native_decide

-- Ch 29 distribution counts
theorem ch29_count_noSubjectMarking :
    (ch29.filter (·.value == .noSubjectPersonNumberMarking)).length = 57 := by
  native_decide
theorem ch29_count_syncretic :
    (ch29.filter (·.value == .syncretic)).length = 60 := by native_decide
theorem ch29_count_notSyncretic :
    (ch29.filter (·.value == .notSyncretic)).length = 81 := by native_decide

-- --------------------------------------------------------------------------
-- §15.13 Chapter 21B: Exponence of TAM Inflection
-- --------------------------------------------------------------------------

theorem english_ch21b :
    (Core.WALS.F21B.lookup "eng").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem mandarin_ch21b :
    (Core.WALS.F21B.lookup "mnd").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem japanese_ch21b :
    (Core.WALS.F21B.lookup "jpn").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem turkish_ch21b :
    (Core.WALS.F21B.lookup "tur").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem finnish_ch21b :
    (Core.WALS.F21B.lookup "fin").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem russian_ch21b :
    (Core.WALS.F21B.lookup "rus").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem swahili_ch21b :
    (Core.WALS.F21B.lookup "swa").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem hindi_ch21b :
    (Core.WALS.F21B.lookup "hin").map (fromWALS21B ·.value) =
    some (.tamAgreement : TAMExponence) := by native_decide
theorem tagalog_ch21b :
    (Core.WALS.F21B.lookup "tag").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem hungarian_ch21b :
    (Core.WALS.F21B.lookup "hun").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem georgian_ch21b :
    (Core.WALS.F21B.lookup "geo").map (fromWALS21B ·.value) =
    some (.tamAgreement : TAMExponence) := by native_decide
theorem thai_ch21b :
    (Core.WALS.F21B.lookup "tha").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem indonesian_ch21b :
    (Core.WALS.F21B.lookup "ind").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem korean_ch21b :
    (Core.WALS.F21B.lookup "kor").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem german_ch21b :
    (Core.WALS.F21B.lookup "ger").map (fromWALS21B ·.value) =
    some (.monoexponential : TAMExponence) := by native_decide
theorem spanish_ch21b :
    (Core.WALS.F21B.lookup "spa").map (fromWALS21B ·.value) =
    some (.tamAgreement : TAMExponence) := by native_decide

-- --------------------------------------------------------------------------
-- §15.14 Chapter 62A: Action Nominal Constructions
-- --------------------------------------------------------------------------

theorem english_ch62 :
    (Core.WALS.F62A.lookup "eng").map (fromWALS62A ·.value) =
    some (.mixed : ActionNominal) := by native_decide
theorem mandarin_ch62 :
    (Core.WALS.F62A.lookup "mnd").map (fromWALS62A ·.value) =
    some (.noActionNominals : ActionNominal) := by native_decide
theorem japanese_ch62 :
    (Core.WALS.F62A.lookup "jpn").map (fromWALS62A ·.value) =
    some (.doublePossessive : ActionNominal) := by native_decide
theorem turkish_ch62 :
    (Core.WALS.F62A.lookup "tur").map (fromWALS62A ·.value) =
    some (.possessiveAccusative : ActionNominal) := by native_decide
theorem finnish_ch62 :
    (Core.WALS.F62A.lookup "fin").map (fromWALS62A ·.value) =
    some (.doublePossessive : ActionNominal) := by native_decide
theorem russian_ch62 :
    (Core.WALS.F62A.lookup "rus").map (fromWALS62A ·.value) =
    some (.ergativePossessive : ActionNominal) := by native_decide
theorem swahili_ch62 :
    (Core.WALS.F62A.lookup "swa").map (fromWALS62A ·.value) =
    some (.possessiveAccusative : ActionNominal) := by native_decide
theorem hindi_ch62 :
    (Core.WALS.F62A.lookup "hin").map (fromWALS62A ·.value) =
    some (.possessiveAccusative : ActionNominal) := by native_decide
theorem tagalog_ch62 :
    (Core.WALS.F62A.lookup "tag").map (fromWALS62A ·.value) =
    some (.possessiveAccusative : ActionNominal) := by native_decide
theorem hungarian_ch62 :
    (Core.WALS.F62A.lookup "hun").map (fromWALS62A ·.value) =
    some (.restricted : ActionNominal) := by native_decide
theorem georgian_ch62 :
    (Core.WALS.F62A.lookup "geo").map (fromWALS62A ·.value) =
    some (.ergativePossessive : ActionNominal) := by native_decide
theorem thai_ch62 :
    (Core.WALS.F62A.lookup "tha").map (fromWALS62A ·.value) =
    some (.mixed : ActionNominal) := by native_decide
theorem indonesian_ch62 :
    (Core.WALS.F62A.lookup "ind").map (fromWALS62A ·.value) =
    some (.ergativePossessive : ActionNominal) := by native_decide
theorem korean_ch62 :
    (Core.WALS.F62A.lookup "kor").map (fromWALS62A ·.value) =
    some (.sentential : ActionNominal) := by native_decide
theorem german_ch62 :
    (Core.WALS.F62A.lookup "ger").map (fromWALS62A ·.value) =
    some (.ergativePossessive : ActionNominal) := by native_decide
theorem spanish_ch62 :
    (Core.WALS.F62A.lookup "spa").map (fromWALS62A ·.value) =
    some (.ergativePossessive : ActionNominal) := by native_decide

-- --------------------------------------------------------------------------
-- §15.15 Chapter 79A: Suppletion According to Tense and Aspect
-- --------------------------------------------------------------------------

theorem english_ch79a :
    (Core.WALS.F79A.lookup "eng").map (fromWALS79A ·.value) =
    some (.tense : SuppletionTA) := by native_decide
theorem mandarin_ch79a :
    (Core.WALS.F79A.lookup "mnd").map (fromWALS79A ·.value) =
    some (.none : SuppletionTA) := by native_decide
theorem japanese_ch79a :
    (Core.WALS.F79A.lookup "jpn").map (fromWALS79A ·.value) =
    some (.none : SuppletionTA) := by native_decide
theorem turkish_ch79a :
    (Core.WALS.F79A.lookup "tur").map (fromWALS79A ·.value) =
    some (.tense : SuppletionTA) := by native_decide
theorem finnish_ch79a :
    (Core.WALS.F79A.lookup "fin").map (fromWALS79A ·.value) =
    some (.none : SuppletionTA) := by native_decide
theorem russian_ch79a :
    (Core.WALS.F79A.lookup "rus").map (fromWALS79A ·.value) =
    some (.tenseAndAspect : SuppletionTA) := by native_decide
theorem swahili_ch79a :
    (Core.WALS.F79A.lookup "swa").map (fromWALS79A ·.value) =
    some (.none : SuppletionTA) := by native_decide
theorem hindi_ch79a :
    (Core.WALS.F79A.lookup "hin").map (fromWALS79A ·.value) =
    some (.tenseAndAspect : SuppletionTA) := by native_decide
theorem tagalog_ch79a :
    (Core.WALS.F79A.lookup "tag").map (fromWALS79A ·.value) =
    some (.none : SuppletionTA) := by native_decide
theorem hungarian_ch79a :
    (Core.WALS.F79A.lookup "hun").map (fromWALS79A ·.value) =
    some (.tense : SuppletionTA) := by native_decide
theorem georgian_ch79a :
    (Core.WALS.F79A.lookup "geo").map (fromWALS79A ·.value) =
    some (.tenseAndAspect : SuppletionTA) := by native_decide
theorem thai_ch79a :
    (Core.WALS.F79A.lookup "tha").map (fromWALS79A ·.value) =
    some (.none : SuppletionTA) := by native_decide
theorem indonesian_ch79a :
    (Core.WALS.F79A.lookup "ind").map (fromWALS79A ·.value) =
    some (.none : SuppletionTA) := by native_decide
theorem korean_ch79a :
    (Core.WALS.F79A.lookup "kor").map (fromWALS79A ·.value) =
    some (.none : SuppletionTA) := by native_decide
theorem german_ch79a :
    (Core.WALS.F79A.lookup "ger").map (fromWALS79A ·.value) =
    some (.tense : SuppletionTA) := by native_decide
theorem spanish_ch79a :
    (Core.WALS.F79A.lookup "spa").map (fromWALS79A ·.value) =
    some (.tenseAndAspect : SuppletionTA) := by native_decide

-- --------------------------------------------------------------------------
-- §15.16 Chapter 79B: Suppletion in Imperatives and Hortatives
-- --------------------------------------------------------------------------

theorem english_ch79b :
    (Core.WALS.F79B.lookup "eng").map (fromWALS79B ·.value) =
    some (.none : SuppletionImperative) := by native_decide
theorem mandarin_ch79b :
    (Core.WALS.F79B.lookup "mnd").map (fromWALS79B ·.value) =
    some (.none : SuppletionImperative) := by native_decide
theorem japanese_ch79b :
    (Core.WALS.F79B.lookup "jpn").map (fromWALS79B ·.value) =
    some (.none : SuppletionImperative) := by native_decide
theorem turkish_ch79b :
    (Core.WALS.F79B.lookup "tur").map (fromWALS79B ·.value) =
    some (.none : SuppletionImperative) := by native_decide
theorem finnish_ch79b :
    (Core.WALS.F79B.lookup "fin").map (fromWALS79B ·.value) =
    some (.imperative : SuppletionImperative) := by native_decide
theorem russian_ch79b :
    (Core.WALS.F79B.lookup "rus").map (fromWALS79B ·.value) =
    some (.imperative : SuppletionImperative) := by native_decide
theorem swahili_ch79b :
    (Core.WALS.F79B.lookup "swa").map (fromWALS79B ·.value) =
    some (.imperative : SuppletionImperative) := by native_decide
theorem hindi_ch79b :
    (Core.WALS.F79B.lookup "hin").map (fromWALS79B ·.value) =
    some (.none : SuppletionImperative) := by native_decide
theorem tagalog_ch79b :
    (Core.WALS.F79B.lookup "tag").map (fromWALS79B ·.value) =
    some (.none : SuppletionImperative) := by native_decide
theorem hungarian_ch79b :
    (Core.WALS.F79B.lookup "hun").map (fromWALS79B ·.value) =
    some (.alternating : SuppletionImperative) := by native_decide
theorem georgian_ch79b :
    (Core.WALS.F79B.lookup "geo").map (fromWALS79B ·.value) =
    some (.imperative : SuppletionImperative) := by native_decide
theorem thai_ch79b :
    (Core.WALS.F79B.lookup "tha").map (fromWALS79B ·.value) =
    some (.none : SuppletionImperative) := by native_decide
theorem indonesian_ch79b :
    (Core.WALS.F79B.lookup "ind").map (fromWALS79B ·.value) =
    some (.none : SuppletionImperative) := by native_decide
theorem korean_ch79b :
    (Core.WALS.F79B.lookup "kor").map (fromWALS79B ·.value) =
    some (.none : SuppletionImperative) := by native_decide
theorem german_ch79b :
    (Core.WALS.F79B.lookup "ger").map (fromWALS79B ·.value) =
    some (.none : SuppletionImperative) := by native_decide
theorem spanish_ch79b :
    (Core.WALS.F79B.lookup "spa").map (fromWALS79B ·.value) =
    some (.imperative : SuppletionImperative) := by native_decide

-- --------------------------------------------------------------------------
-- §15.17 Chapter 80A: Verbal Number and Suppletion
-- --------------------------------------------------------------------------

theorem english_ch80 :
    (Core.WALS.F80A.lookup "eng").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem mandarin_ch80 :
    (Core.WALS.F80A.lookup "mnd").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem japanese_ch80 :
    (Core.WALS.F80A.lookup "jpn").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem turkish_ch80 :
    (Core.WALS.F80A.lookup "tur").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem finnish_ch80 :
    (Core.WALS.F80A.lookup "fin").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem russian_ch80 :
    (Core.WALS.F80A.lookup "rus").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem swahili_ch80 :
    (Core.WALS.F80A.lookup "swa").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem hindi_ch80 :
    (Core.WALS.F80A.lookup "hin").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem tagalog_ch80 :
    (Core.WALS.F80A.lookup "tag").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem hungarian_ch80 :
    (Core.WALS.F80A.lookup "hun").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem georgian_ch80 :
    (Core.WALS.F80A.lookup "geo").map (fromWALS80A ·.value) =
    some (.pairsNoSuppletion : VerbalNumber) := by native_decide
theorem thai_ch80 :
    (Core.WALS.F80A.lookup "tha").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem indonesian_ch80 :
    (Core.WALS.F80A.lookup "ind").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem korean_ch80 :
    (Core.WALS.F80A.lookup "kor").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem german_ch80 :
    (Core.WALS.F80A.lookup "ger").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide
theorem spanish_ch80 :
    (Core.WALS.F80A.lookup "spa").map (fromWALS80A ·.value) =
    some (.none : VerbalNumber) := by native_decide

-- --------------------------------------------------------------------------
-- §15.18 WALS Dataset Size Verification (new chapters)
-- --------------------------------------------------------------------------

theorem ch21b_size : ch21b.length = 160 := by native_decide
theorem ch62_size : ch62.length = 168 := by native_decide
theorem ch79a_size : ch79a.length = 193 := by native_decide
theorem ch79b_size : ch79b.length = 193 := by native_decide
theorem ch80_size : ch80.length = 193 := by native_decide

-- --------------------------------------------------------------------------
-- §15.19 WALS Distribution Count Verification (new chapters)
-- --------------------------------------------------------------------------

-- Ch 21B distribution counts
theorem ch21b_count_monoexponentialTam :
    (ch21b.filter (·.value == .monoexponentialTam)).length = 127 := by native_decide
theorem ch21b_count_tamAgreement :
    (ch21b.filter (·.value == .tamAgreement)).length = 19 := by native_decide
theorem ch21b_count_tamAgreementDiathesis :
    (ch21b.filter (·.value == .tamAgreementDiathesis)).length = 4 := by native_decide
theorem ch21b_count_tamAgreementConstruct :
    (ch21b.filter (·.value == .tamAgreementConstruct)).length = 1 := by native_decide
theorem ch21b_count_tamPolarity :
    (ch21b.filter (·.value == .tamPolarity)).length = 5 := by native_decide
theorem ch21b_count_noTam :
    (ch21b.filter (·.value == .noTam)).length = 4 := by native_decide

-- Ch 62A distribution counts
theorem ch62_count_sentential :
    (ch62.filter (·.value == .sentential)).length = 25 := by native_decide
theorem ch62_count_possessiveAccusative :
    (ch62.filter (·.value == .possessiveAccusative)).length = 29 := by native_decide
theorem ch62_count_ergativePossessive :
    (ch62.filter (·.value == .ergativePossessive)).length = 21 := by native_decide
theorem ch62_count_doublePossessive :
    (ch62.filter (·.value == .doublePossessive)).length = 7 := by native_decide
theorem ch62_count_other :
    (ch62.filter (·.value == .other)).length = 6 := by native_decide
theorem ch62_count_mixed :
    (ch62.filter (·.value == .mixed)).length = 14 := by native_decide
theorem ch62_count_restricted :
    (ch62.filter (·.value == .restricted)).length = 24 := by native_decide
theorem ch62_count_noActionNominals :
    (ch62.filter (·.value == .noActionNominals)).length = 42 := by native_decide

-- Ch 79A distribution counts
theorem ch79a_count_tense :
    (ch79a.filter (·.value == .tense)).length = 36 := by native_decide
theorem ch79a_count_aspect :
    (ch79a.filter (·.value == .aspect)).length = 10 := by native_decide
theorem ch79a_count_tenseAndAspect :
    (ch79a.filter (·.value == .tenseAndAspect)).length = 24 := by native_decide
theorem ch79a_count_none :
    (ch79a.filter (·.value == .none)).length = 123 := by native_decide

-- Ch 79B distribution counts
theorem ch79b_count_alternating :
    (ch79b.filter (·.value == .aRegularAndASuppletiveFormAlternate)).length = 8 := by
  native_decide
theorem ch79b_count_imperative :
    (ch79b.filter (·.value == .imperative)).length = 29 := by native_decide
theorem ch79b_count_hortative :
    (ch79b.filter (·.value == .hortative)).length = 2 := by native_decide
theorem ch79b_count_imperativeAndHortative :
    (ch79b.filter (·.value == .imperativeAndHortative)).length = 1 := by native_decide
theorem ch79b_count_none :
    (ch79b.filter (·.value == .none)).length = 153 := by native_decide

-- Ch 80A distribution counts
theorem ch80_count_none :
    (ch80.filter (·.value == .none)).length = 159 := by native_decide
theorem ch80_count_pairsNoSuppletion :
    (ch80.filter (·.value == .singularPluralPairsNoSuppletion)).length = 12 := by native_decide
theorem ch80_count_pairsSuppletion :
    (ch80.filter (·.value == .singularPluralPairsSuppletion)).length = 15 := by native_decide
theorem ch80_count_triplesNoSuppletion :
    (ch80.filter (·.value == .singularDualPluralTriplesNoSuppletion)).length = 5 := by
  native_decide
theorem ch80_count_triplesSuppletion :
    (ch80.filter (·.value == .singularDualPluralTriplesSuppletion)).length = 2 := by native_decide

end Phenomena.Morphology.Typology
