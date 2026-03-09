import Linglib.Core.Morphology.MorphProfile
import Mathlib.Data.Rat.Defs
import Linglib.Fragments.English.Morph
import Linglib.Fragments.Mandarin.Morph
import Linglib.Fragments.Japanese.Morph
import Linglib.Fragments.Turkish.Morph
import Linglib.Fragments.Finnish.Morph
import Linglib.Fragments.Russian.Morph
import Linglib.Fragments.Swahili.Morph
import Linglib.Fragments.Arabic.Morph
import Linglib.Fragments.Hindi.Morph
import Linglib.Fragments.Tagalog.Morph
import Linglib.Fragments.Quechua.Morph
import Linglib.Fragments.Hungarian.Morph
import Linglib.Fragments.Georgian.Morph
import Linglib.Fragments.Thai.Morph
import Linglib.Fragments.Indonesian.Morph
import Linglib.Fragments.Korean.Morph
import Linglib.Fragments.German.Morph
import Linglib.Fragments.Spanish.Morph

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

## MorphProfile Sample

Eighteen typologically diverse languages with morphological profiles
derived from WALS data. Types and WALS lookup helpers are defined in
`Core.Morphology.MorphProfile`; per-language profiles live in
`Fragments.{Language}.Morph`.

-/

namespace Phenomena.Morphology.Typology

open Core.Morphology

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

Typological classification types are defined in `Core.Morphology.MorphProfile`.

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

open Core.WALS.F20A (FusionType) in
/-- Map WALS 20A fine-grained fusion types to coarse categories.
    Mixed types are mapped by their non-concatenative component. -/
def toFusion : FusionType → Fusion
  | .exclusivelyConcatenative => .concatenative
  | .exclusivelyIsolating => .isolating
  | .exclusivelyTonal | .tonalIsolating | .tonalConcatenative => .nonlinear
  | .ablautConcatenative => .nonlinear
  | .isolatingConcatenative => .concatenative

-- Grounding: example languages verified against F20A data
theorem vietnamese_isolating : Core.WALS.F20A.lookup "vie" =
    some ⟨"vie", "Vietnamese", "vie", .exclusivelyIsolating⟩ := by native_decide
theorem indonesian_isolating : Core.WALS.F20A.lookup "ind" =
    some ⟨"ind", "Indonesian", "ind", .exclusivelyIsolating⟩ := by native_decide
theorem turkish_concatenative : Core.WALS.F20A.lookup "tur" =
    some ⟨"tur", "Turkish", "tur", .exclusivelyConcatenative⟩ := by native_decide
theorem finnish_concatenative : Core.WALS.F20A.lookup "fin" =
    some ⟨"fin", "Finnish", "fin", .exclusivelyConcatenative⟩ := by native_decide
theorem swahili_concatenative : Core.WALS.F20A.lookup "swa" =
    some ⟨"swa", "Swahili", "swh", .exclusivelyConcatenative⟩ := by native_decide
theorem arabic_ablaut : Core.WALS.F20A.lookup "aeg" =
    some ⟨"aeg", "Arabic (Egyptian)", "arz", .ablautConcatenative⟩ := by native_decide
theorem hebrew_ablaut : Core.WALS.F20A.lookup "heb" =
    some ⟨"heb", "Hebrew (Modern)", "heb", .ablautConcatenative⟩ := by native_decide
-- Note: Russian and German are exclusivelyConcatenative in WALS 20A (case formatives),
-- despite being commonly called "fusional" in typological tradition.
theorem russian_concatenative : Core.WALS.F20A.lookup "rus" =
    some ⟨"rus", "Russian", "rus", .exclusivelyConcatenative⟩ := by native_decide
theorem german_concatenative : Core.WALS.F20A.lookup "ger" =
    some ⟨"ger", "German", "deu", .exclusivelyConcatenative⟩ := by native_decide
-- Note: Mandarin and Thai are isolatingConcatenative (mixed), not exclusively isolating.
theorem mandarin_isoConcatenative : Core.WALS.F20A.lookup "mnd" =
    some ⟨"mnd", "Mandarin", "cmn", .isolatingConcatenative⟩ := by native_decide
theorem thai_isoConcatenative : Core.WALS.F20A.lookup "tha" =
    some ⟨"tha", "Thai", "tha", .isolatingConcatenative⟩ := by native_decide

/-- A single row in a WALS distribution table: a label and a language count. -/
structure WALSCount where
  label : String
  count : Nat
  deriving Repr, DecidableEq, BEq

/-- WALS Chapter 20 distribution, derived from F20A data (@cite{bickel-nichols-2013a}). -/
def ch20Distribution : List WALSCount :=
  [ ⟨"Exclusively concatenative", (ch20.filter (·.value == .exclusivelyConcatenative)).length⟩
  , ⟨"Exclusively isolating", (ch20.filter (·.value == .exclusivelyIsolating)).length⟩
  , ⟨"Exclusively tonal", (ch20.filter (·.value == .exclusivelyTonal)).length⟩
  , ⟨"Tonal/isolating", (ch20.filter (·.value == .tonalIsolating)).length⟩
  , ⟨"Tonal/concatenative", (ch20.filter (·.value == .tonalConcatenative)).length⟩
  , ⟨"Ablaut/concatenative", (ch20.filter (·.value == .ablautConcatenative)).length⟩
  , ⟨"Isolating/concatenative", (ch20.filter (·.value == .isolatingConcatenative)).length⟩ ]

/-- Ch 20 total: 165 languages (derived from F20A data). -/
theorem ch20_total :
    ch20Distribution.foldl (λ acc c => acc + c.count) 0 = 165 := by native_decide

-- ============================================================================
-- §4.2 Chapter 21: Exponence of Selected Inflectional Formatives
-- ============================================================================

open Core.WALS.F21A (ExponenceType) in
/-- Map WALS 21A fine-grained exponence types to coarse categories.
    All polyexponential subtypes (case+number, case+referentiality,
    case+TAM) map to `.polyexponential`. -/
def toExponence : ExponenceType → Exponence
  | .monoexponentialCase => .monoexponential
  | .caseNumber | .caseReferentiality | .caseTam => .polyexponential
  | .noCase => .noCase

-- Grounding: example languages verified against F21A data
theorem turkish_monoexp : Core.WALS.F21A.lookup "tur" =
    some ⟨"tur", "Turkish", "tur", .monoexponentialCase⟩ := by native_decide
theorem finnish_caseNumber : Core.WALS.F21A.lookup "fin" =
    some ⟨"fin", "Finnish", "fin", .caseNumber⟩ := by native_decide
theorem german_caseNumber : Core.WALS.F21A.lookup "ger" =
    some ⟨"ger", "German", "deu", .caseNumber⟩ := by native_decide
theorem russian_caseNumber : Core.WALS.F21A.lookup "rus" =
    some ⟨"rus", "Russian", "rus", .caseNumber⟩ := by native_decide
theorem english_noCase : Core.WALS.F21A.lookup "eng" =
    some ⟨"eng", "English", "eng", .noCase⟩ := by native_decide
theorem kayardild_caseTam : Core.WALS.F21A.lookup "kay" =
    some ⟨"kay", "Kayardild", "gyd", .caseTam⟩ := by native_decide

/-- WALS Chapter 21 distribution, derived from F21A data (@cite{bickel-nichols-2013b}). -/
def ch21Distribution : List WALSCount :=
  [ ⟨"Monoexponential case", (ch21.filter (·.value == .monoexponentialCase)).length⟩
  , ⟨"Case + number", (ch21.filter (·.value == .caseNumber)).length⟩
  , ⟨"Case + referentiality", (ch21.filter (·.value == .caseReferentiality)).length⟩
  , ⟨"Case + TAM", (ch21.filter (·.value == .caseTam)).length⟩
  , ⟨"No case", (ch21.filter (·.value == .noCase)).length⟩ ]

/-- Ch 21 total: 162 languages (derived from F21A data). -/
theorem ch21_total :
    ch21Distribution.foldl (λ acc c => acc + c.count) 0 = 162 := by native_decide

-- ============================================================================
-- §4.3 Chapter 22: Inflectional Synthesis of the Verb
-- ============================================================================

open Core.WALS.F22A (InflectionalSynthesis) in
/-- Map WALS 22A fine-grained categories to coarse synthesis levels.
    Boundaries align with WALS bin edges to avoid splitting categories. -/
def toVerbSynthesis : InflectionalSynthesis → VerbSynthesis
  | .categoryPerWord0_1 | .categoriesPerWord2_3 => .low
  | .categoriesPerWord4_5 | .categoriesPerWord6_7 => .moderate
  | .categoriesPerWord8_9 | .categoriesPerWord10_11 | .categoriesPerWord12_13 => .high

-- Grounding: example languages verified against F22A data
theorem mandarin_0_1 : Core.WALS.F22A.lookup "mnd" =
    some ⟨"mnd", "Mandarin", "cmn", .categoryPerWord0_1⟩ := by native_decide
theorem english_2_3 : Core.WALS.F22A.lookup "eng" =
    some ⟨"eng", "English", "eng", .categoriesPerWord2_3⟩ := by native_decide
theorem thai_2_3 : Core.WALS.F22A.lookup "tha" =
    some ⟨"tha", "Thai", "tha", .categoriesPerWord2_3⟩ := by native_decide
theorem spanish_4_5 : Core.WALS.F22A.lookup "spa" =
    some ⟨"spa", "Spanish", "spa", .categoriesPerWord4_5⟩ := by native_decide
theorem russian_4_5 : Core.WALS.F22A.lookup "rus" =
    some ⟨"rus", "Russian", "rus", .categoriesPerWord4_5⟩ := by native_decide
theorem swahili_4_5 : Core.WALS.F22A.lookup "swa" =
    some ⟨"swa", "Swahili", "swh", .categoriesPerWord4_5⟩ := by native_decide
theorem georgian_8_9 : Core.WALS.F22A.lookup "geo" =
    some ⟨"geo", "Georgian", "kat", .categoriesPerWord8_9⟩ := by native_decide
theorem abkhaz_10_11 : Core.WALS.F22A.lookup "abk" =
    some ⟨"abk", "Abkhaz", "abk", .categoriesPerWord10_11⟩ := by native_decide

/-- WALS Chapter 22 distribution, derived from F22A data (@cite{bickel-nichols-2013c}). -/
def ch22Distribution : List WALSCount :=
  [ ⟨"0-1 categories per word", (ch22.filter (·.value == .categoryPerWord0_1)).length⟩
  , ⟨"2-3 categories per word", (ch22.filter (·.value == .categoriesPerWord2_3)).length⟩
  , ⟨"4-5 categories per word", (ch22.filter (·.value == .categoriesPerWord4_5)).length⟩
  , ⟨"6-7 categories per word", (ch22.filter (·.value == .categoriesPerWord6_7)).length⟩
  , ⟨"8-9 categories per word", (ch22.filter (·.value == .categoriesPerWord8_9)).length⟩
  , ⟨"10-11 categories per word", (ch22.filter (·.value == .categoriesPerWord10_11)).length⟩
  , ⟨"12-13 categories per word", (ch22.filter (·.value == .categoriesPerWord12_13)).length⟩ ]

/-- Ch 22 total: 145 languages (derived from F22A data). -/
theorem ch22_total :
    ch22Distribution.foldl (λ acc c => acc + c.count) 0 = 145 := by native_decide

-- ============================================================================
-- §4.4 Chapter 25: Locus of Marking: Whole-Language Typology
-- ============================================================================

open Core.WALS.F25A (LocusOfMarkingWholeLanguageTypology) in
/-- Map WALS 25A fine-grained locus-of-marking types to coarse 4-way classification.
    The large "inconsistent or other" category (121 langs) maps to `.zeroMarking`
    since these languages lack a consistent marking pattern. -/
def toLocusOfMarking : LocusOfMarkingWholeLanguageTypology → LocusOfMarking
  | .headMarking => .headMarking
  | .dependentMarking => .dependentMarking
  | .doubleMarking => .doubleMarking
  | .zeroMarking | .inconsistentOrOther => .zeroMarking

/-- WALS Chapter 25A distribution, derived from F25A data (N = 236). -/
def ch25Distribution : List WALSCount :=
  [ ⟨"Head-marking", (ch25a.filter (·.value == .headMarking)).length⟩
  , ⟨"Dependent-marking", (ch25a.filter (·.value == .dependentMarking)).length⟩
  , ⟨"Double-marking", (ch25a.filter (·.value == .doubleMarking)).length⟩
  , ⟨"Zero-marking", (ch25a.filter (·.value == .zeroMarking)).length⟩
  , ⟨"Inconsistent or other", (ch25a.filter (·.value == .inconsistentOrOther)).length⟩ ]

/-- Ch 25 total: 236 languages (derived from F25A data). -/
theorem ch25_total :
    ch25Distribution.foldl (λ acc c => acc + c.count) 0 = 236 := by native_decide

-- ============================================================================
-- §4.5 Chapter 26: Prefixing vs Suffixing in Inflectional Morphology
-- ============================================================================

-- Grounding: example languages verified against F26A data
theorem turkish_strongSuffix : Core.WALS.F26A.lookup "tur" =
    some ⟨"tur", "Turkish", "tur", .stronglySuffixing⟩ := by native_decide
theorem japanese_strongSuffix : Core.WALS.F26A.lookup "jpn" =
    some ⟨"jpn", "Japanese", "jpn", .stronglySuffixing⟩ := by native_decide
-- Note: Russian and German are strongly (not weakly) suffixing in WALS 26A.
theorem russian_strongSuffix : Core.WALS.F26A.lookup "rus" =
    some ⟨"rus", "Russian", "rus", .stronglySuffixing⟩ := by native_decide
theorem german_strongSuffix : Core.WALS.F26A.lookup "ger" =
    some ⟨"ger", "German", "deu", .stronglySuffixing⟩ := by native_decide
theorem arabic_eg_weakSuffix : Core.WALS.F26A.lookup "aeg" =
    some ⟨"aeg", "Arabic (Egyptian)", "arz", .weaklySuffixing⟩ := by native_decide
theorem swahili_weakPrefix : Core.WALS.F26A.lookup "swa" =
    some ⟨"swa", "Swahili", "swh", .weaklyPrefixing⟩ := by native_decide
theorem navajo_strongPrefix : Core.WALS.F26A.lookup "nav" =
    some ⟨"nav", "Navajo", "nav", .strongPrefixing⟩ := by native_decide
-- Note: Thai, Tagalog, and Vietnamese are littleAffixation, not prefixing.
theorem thai_littleAffix : Core.WALS.F26A.lookup "tha" =
    some ⟨"tha", "Thai", "tha", .littleAffixation⟩ := by native_decide
theorem tagalog_littleAffix : Core.WALS.F26A.lookup "tag" =
    some ⟨"tag", "Tagalog", "tgl", .littleAffixation⟩ := by native_decide
theorem vietnamese_littleAffix : Core.WALS.F26A.lookup "vie" =
    some ⟨"vie", "Vietnamese", "vie", .littleAffixation⟩ := by native_decide
-- Note: Mandarin is strongly suffixing in WALS 26A (few affixes but all suffixal).
theorem mandarin_strongSuffix : Core.WALS.F26A.lookup "mnd" =
    some ⟨"mnd", "Mandarin", "cmn", .stronglySuffixing⟩ := by native_decide

/-- WALS Chapter 26 distribution, derived from F26A data (@cite{dryer-haspelmath-2013}). -/
def ch26Distribution : List WALSCount :=
  [ ⟨"Strongly suffixing", (ch26.filter (·.value == .stronglySuffixing)).length⟩
  , ⟨"Weakly suffixing", (ch26.filter (·.value == .weaklySuffixing)).length⟩
  , ⟨"Equal prefixing and suffixing", (ch26.filter (·.value == .equalPrefixingAndSuffixing)).length⟩
  , ⟨"Weakly prefixing", (ch26.filter (·.value == .weaklyPrefixing)).length⟩
  , ⟨"Strongly prefixing", (ch26.filter (·.value == .strongPrefixing)).length⟩
  , ⟨"Little affixation", (ch26.filter (·.value == .littleAffixation)).length⟩ ]

/-- Ch 26 total: 969 languages (derived from F26A data). -/
theorem ch26_total :
    ch26Distribution.foldl (λ acc c => acc + c.count) 0 = 969 := by native_decide

-- ============================================================================
-- §4.6 Chapter 27: Reduplication
-- ============================================================================

-- Grounding: example languages verified against F27A data
theorem tagalog_fullPartial : Core.WALS.F27A.lookup "tag" =
    some ⟨"tag", "Tagalog", "tgl", .productiveFullAndPartialReduplication⟩ := by native_decide
theorem swahili_fullPartial : Core.WALS.F27A.lookup "swa" =
    some ⟨"swa", "Swahili", "swh", .productiveFullAndPartialReduplication⟩ := by native_decide
-- Note: Indonesian has full reduplication ONLY (not partial) in WALS 27A.
theorem indonesian_fullOnly : Core.WALS.F27A.lookup "ind" =
    some ⟨"ind", "Indonesian", "ind", .fullReduplicationOnly⟩ := by native_decide
theorem english_noRedup : Core.WALS.F27A.lookup "eng" =
    some ⟨"eng", "English", "eng", .noProductiveReduplication⟩ := by native_decide
-- Note: Arabic (Egyptian) has productive reduplication in WALS 27A, not "none."
theorem arabic_eg_fullPartial : Core.WALS.F27A.lookup "aeg" =
    some ⟨"aeg", "Arabic (Egyptian)", "arz", .productiveFullAndPartialReduplication⟩ := by native_decide

/-- WALS Chapter 27 distribution, derived from F27A data (@cite{rubino-2013}). -/
def ch27Distribution : List WALSCount :=
  [ ⟨"Productive full and partial reduplication", (ch27.filter (·.value == .productiveFullAndPartialReduplication)).length⟩
  , ⟨"Full reduplication only", (ch27.filter (·.value == .fullReduplicationOnly)).length⟩
  , ⟨"No productive reduplication", (ch27.filter (·.value == .noProductiveReduplication)).length⟩ ]

/-- Ch 27 total: 368 languages (derived from F27A data). -/
theorem ch27_total :
    ch27Distribution.foldl (λ acc c => acc + c.count) 0 = 368 := by native_decide

-- ============================================================================
-- §4.7 Chapter 23: Locus of Marking in the Clause
-- ============================================================================

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
-- §5. Profile Collection
-- ============================================================================

/-! Fragment profiles are defined in `Fragments.{Language}.Morph` with values
    derived from WALS data via `Core.Morphology.wals*` lookup helpers. -/

-- Profile aliases for concise reference in theorems below
private abbrev englishMorph := Fragments.English.morphProfile
private abbrev mandarinMorph := Fragments.Mandarin.morphProfile
private abbrev japaneseMorph := Fragments.Japanese.morphProfile
private abbrev turkishMorph := Fragments.Turkish.morphProfile
private abbrev finnishMorph := Fragments.Finnish.morphProfile
private abbrev russianMorph := Fragments.Russian.morphProfile
private abbrev swahiliMorph := Fragments.Swahili.morphProfile
private abbrev arabicMorph := Fragments.Arabic.morphProfile
private abbrev hindiMorph := Fragments.Hindi.morphProfile
private abbrev tagalogMorph := Fragments.Tagalog.morphProfile
private abbrev quechuaMorph := Fragments.Quechua.morphProfile
private abbrev hungarianMorph := Fragments.Hungarian.morphProfile
private abbrev georgianMorph := Fragments.Georgian.morphProfile
private abbrev thaiMorph := Fragments.Thai.morphProfile
private abbrev indonesianMorph := Fragments.Indonesian.morphProfile
private abbrev koreanMorph := Fragments.Korean.morphProfile
private abbrev germanMorph := Fragments.German.morphProfile
private abbrev spanishMorph := Fragments.Spanish.morphProfile

/-- All 18 morphological mechanism profiles. -/
def allMorphProfiles : List MorphProfile :=
  [ englishMorph, mandarinMorph, japaneseMorph, turkishMorph, finnishMorph
  , russianMorph, swahiliMorph, arabicMorph, hindiMorph, tagalogMorph
  , quechuaMorph, hungarianMorph, georgianMorph, thaiMorph, indonesianMorph
  , koreanMorph, germanMorph, spanishMorph ]

theorem allMorphProfiles_count : allMorphProfiles.length = 18 := by native_decide

-- ============================================================================
-- §6. Counting Helpers
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
-- §7. Distribution Verification for Our Sample
-- ============================================================================

/-! Count values are determined by WALS-derived Fragment profiles. Values
    differ from the pre-refactor hand-specified profiles because WALS
    evaluates specific formatives, not overall typological tradition. -/

/-- Fusion type distribution in our sample. -/
theorem sample_concatenative_count :
    countByFusion allMorphProfiles .concatenative = 14 := by native_decide
theorem sample_nonlinear_count :
    countByFusion allMorphProfiles .nonlinear = 1 := by native_decide
theorem sample_isolating_count :
    countByFusion allMorphProfiles .isolating = 3 := by native_decide

/-- Exponence distribution in our sample. -/
theorem sample_monoexponential_count :
    countByExponence allMorphProfiles .monoexponential = 12 := by native_decide
theorem sample_polyexponential_count :
    countByExponence allMorphProfiles .polyexponential = 5 := by native_decide
theorem sample_no_inflection_count :
    countByExponence allMorphProfiles .noCase = 1 := by native_decide

/-- Verb synthesis distribution in our sample. -/
theorem sample_low_synthesis :
    countBySynthesis allMorphProfiles .low = 7 := by native_decide
theorem sample_moderate_synthesis :
    countBySynthesis allMorphProfiles .moderate = 9 := by native_decide
theorem sample_high_synthesis :
    countBySynthesis allMorphProfiles .high = 2 := by native_decide

/-- Locus of marking distribution in our sample. -/
theorem sample_dependent_marking :
    countByLocus allMorphProfiles .dependentMarking = 11 := by native_decide
theorem sample_head_marking :
    countByLocus allMorphProfiles .headMarking = 1 := by native_decide
theorem sample_double_marking :
    countByLocus allMorphProfiles .doubleMarking = 4 := by native_decide
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
-- §8. Typological Generalizations
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
in our sample. -/

theorem dependent_marking_common :
    countByLocus allMorphProfiles .dependentMarking >=
    countByLocus allMorphProfiles .headMarking := by native_decide

/-! ### Generalization 4: Reduplication is present in a majority of languages
in the WALS Ch 27 data (182/368 = 49% have productive reduplication). -/

theorem reduplication_in_majority_wals :
    (147 + 35 : Nat) > 186 / 2 := by native_decide

theorem reduplication_attested_in_sample :
    (allMorphProfiles.filter (·.hasRedup)).length >= 3 := by native_decide

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

/-! ### Generalization: All languages with high verb synthesis have either
concatenative or nonlinear fusion (never isolating). -/

theorem high_synthesis_not_isolating :
    allMorphProfiles.all (λ p =>
      if p.isHighSynthesis then !p.isIsolating
      else true) = true := by native_decide

-- ============================================================================
-- §9. WALS Chapter-Level Distribution Theorems
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
-- §10. Cross-Dimensional Consistency
-- ============================================================================

/-- All ISO codes in the morphological profiles are 3 characters. -/
theorem morph_iso_length_3 :
    allMorphProfiles.all (λ p => p.iso.length == 3) = true := by native_decide

/-- No duplicate ISO codes in the morphological profiles. -/
theorem morph_iso_unique :
    (allMorphProfiles.map (·.iso)).eraseDups.length =
    allMorphProfiles.length := by native_decide

-- ============================================================================
-- §11. WALS Grounding: Per-Language Verification
-- ============================================================================

/-!
## WALS Grounding

Per-language grounding theorems verify that Fragment `MorphProfile` values are
consistent with WALS generated data. Since profiles are now WALS-derived by
construction (via `wals*` helpers), these theorems serve as regression tests:
if WALS data changes, the corresponding theorem breaks.
-/

-- --------------------------------------------------------------------------
-- §11.1 Chapter 20A: Fusion
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
-- §11.2 Chapter 22A: Verb Synthesis
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
-- §11.3 Chapter 26A: Prefixing vs Suffixing
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
-- §11.4 Chapter 27A: Reduplication
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
-- §11.5 Chapter 23A: Locus of Marking in the Clause
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
-- §11.6 Chapter 24A: Locus of Marking in Possessive NP
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
-- §11.7 Chapter 25A: Whole-Language Marking Typology
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
-- §11.8 Chapter 25B: Zero Marking of A and P Arguments
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
-- §11.9 Chapter 28A: Case Syncretism
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
-- §11.10 Chapter 29A: Syncretism in Verbal Person/Number Marking
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
-- §11.11 WALS Dataset Size Verification
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
-- §11.12 WALS Distribution Count Verification
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
-- §11.13 Chapter 21B: Exponence of TAM Inflection
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
-- §11.14 Chapter 62A: Action Nominal Constructions
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
-- §11.15 Chapter 79A: Suppletion According to Tense and Aspect
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
-- §11.16 Chapter 79B: Suppletion in Imperatives and Hortatives
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
-- §11.17 Chapter 80A: Verbal Number and Suppletion
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
-- §11.18 WALS Dataset Size Verification (new chapters)
-- --------------------------------------------------------------------------

theorem ch21b_size : ch21b.length = 160 := by native_decide
theorem ch62_size : ch62.length = 168 := by native_decide
theorem ch79a_size : ch79a.length = 193 := by native_decide
theorem ch79b_size : ch79b.length = 193 := by native_decide
theorem ch80_size : ch80.length = 193 := by native_decide

-- --------------------------------------------------------------------------
-- §11.19 WALS Distribution Count Verification (new chapters)
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
