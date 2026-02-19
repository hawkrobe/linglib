import Mathlib.Data.Rat.Defs

/-!
# Morphological Typology: Paradigm Complexity

Cross-linguistic typological data on morphological paradigm complexity.

## LanguageData

`LanguageData` records summary statistics about a language's inflectional
paradigm system: the number of inflection classes (E-complexity), the
number of paradigm cells, and information-theoretic measures of paradigm
predictability (I-complexity).

## Ackerman & Malouf (2013) Sample

Ten typologically diverse languages from Ackerman & Malouf (2013, Tables
2–3), spanning three phyla, four macro-areas, and a range from 2 to 109
inflection classes. The central empirical finding: despite wildly varying
E-complexity, I-complexity (average conditional entropy) is uniformly low
across all ten languages.

## References

- Ackerman, F. & Malouf, R. (2013). Morphological Organization: The Low
  Conditional Entropy Conjecture. *Language* 89(3), 429–464.
-/

namespace Phenomena.Morphology.Typology

-- ============================================================================
-- §1. Language Data Records
-- ============================================================================

/-- Summary statistics for a language's morphological paradigm system,
    as reported in published studies.

    Fields correspond to Tables 2–3 of Ackerman & Malouf (2013). -/
structure LanguageData where
  /-- Language name -/
  name : String
  /-- Language family -/
  family : String
  /-- Number of inflection classes (E-complexity) -/
  numClasses : Nat
  /-- Number of paradigm cells -/
  numCells : Nat
  /-- Average conditional entropy H̄(Cᵢ|Cⱼ) in bits (I-complexity) -/
  avgCondEntropy : ℚ
  /-- Maximum cell entropy max H(Cᵢ) in bits -/
  maxCellEntropy : ℚ
  deriving Repr

-- ============================================================================
-- §2. Ackerman & Malouf (2013): The Ten Languages
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

/-- Chiquihuitlán Mazatec (Oto-Manguean; Oaxaca, Mexico).
    109 classes, 4 cells. The paper's primary case study (§4). -/
def mazatec : LanguageData where
  name := "Chiquihuitlán Mazatec"
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

/-- All 10 languages in the Ackerman & Malouf (2013) sample (Table 3). -/
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

end Phenomena.Morphology.Typology
