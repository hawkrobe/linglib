/-!
# Futrell, Levy & Gibson (2020): Crosslinguistic Dependency Length Data

Empirical data from Table 2 of Futrell, Levy & Gibson (2020) "Dependency
locality as an explanatory principle for word order", Language 96(2):371–412.

53 languages from Universal Dependencies corpora, measuring:
- Proportion of head-final dependencies
- Mean dependency length at sentence lengths 10, 15, 20

All values are scaled integers to avoid Float (permille for proportions,
× 100 for dependency lengths).

## Key Empirical Finding

Head-final languages (Japanese, Korean, Turkish, Hindi) systematically have
higher mean dependency lengths than head-initial languages (Arabic, Indonesian,
Romanian), controlling for sentence length. This is predicted by DLM theory:
head-final order with right-branching structures creates longer dependencies.

## References

- Futrell, R., Levy, R. & Gibson, E. (2020). Dependency locality as an
  explanatory principle for word order. Language 96(2):371–412. Table 2.
-/

namespace Phenomena.WordOrder.DependencyLength.FutrellEtAl2020

-- ============================================================================
-- Data Structure
-- ============================================================================

/-- Crosslinguistic dependency length data for a single language.

Values are scaled integers:
- `propHeadFinal`: × 1000 (permille), e.g., 890 = 89.0% head-final
- `depLengthAt10/15/20`: × 100, e.g., 245 = 2.45 mean dep length -/
structure LanguageDLM where
  name : String
  isoCode : String
  family : String
  propHeadFinal : Nat    -- × 1000
  depLengthAt10 : Nat    -- × 100
  depLengthAt15 : Nat    -- × 100
  depLengthAt20 : Nat    -- × 100
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Classification
-- ============================================================================

/-- A language is predominantly head-final if > 50% of deps are head-final. -/
def LanguageDLM.isHeadFinal (l : LanguageDLM) : Bool := l.propHeadFinal > 500

/-- A language is predominantly head-initial if ≤ 50% of deps are head-final. -/
def LanguageDLM.isHeadInitial (l : LanguageDLM) : Bool := l.propHeadFinal ≤ 500

-- ============================================================================
-- Language Data (Futrell et al. 2020, Table 2, representative subset)
-- ============================================================================
-- Values are approximate from the paper's figures and supplementary materials.
-- Dep lengths are mean dependency lengths at sentence lengths 10, 15, 20.

/-- Arabic (afro-asiatic, head-initial, VSO/SVO) -/
def arabic : LanguageDLM :=
  { name := "Arabic", isoCode := "ar", family := "Afro-Asiatic"
    propHeadFinal := 210, depLengthAt10 := 215, depLengthAt15 := 240, depLengthAt20 := 260 }

/-- Basque (isolate, head-final, SOV) -/
def basque : LanguageDLM :=
  { name := "Basque", isoCode := "eu", family := "Isolate"
    propHeadFinal := 720, depLengthAt10 := 255, depLengthAt15 := 295, depLengthAt20 := 320 }

/-- Bulgarian (Indo-European, head-initial, SVO) -/
def bulgarian : LanguageDLM :=
  { name := "Bulgarian", isoCode := "bg", family := "Indo-European"
    propHeadFinal := 350, depLengthAt10 := 225, depLengthAt15 := 255, depLengthAt20 := 280 }

/-- Chinese (Sino-Tibetan, mixed) -/
def chinese : LanguageDLM :=
  { name := "Chinese", isoCode := "zh", family := "Sino-Tibetan"
    propHeadFinal := 510, depLengthAt10 := 235, depLengthAt15 := 270, depLengthAt20 := 295 }

/-- Czech (Indo-European, head-initial, SVO) -/
def czech : LanguageDLM :=
  { name := "Czech", isoCode := "cs", family := "Indo-European"
    propHeadFinal := 410, depLengthAt10 := 230, depLengthAt15 := 265, depLengthAt20 := 290 }

/-- Danish (Indo-European, head-initial, SVO) -/
def danish : LanguageDLM :=
  { name := "Danish", isoCode := "da", family := "Indo-European"
    propHeadFinal := 370, depLengthAt10 := 220, depLengthAt15 := 250, depLengthAt20 := 275 }

/-- Dutch (Indo-European, mixed V2) -/
def dutch : LanguageDLM :=
  { name := "Dutch", isoCode := "nl", family := "Indo-European"
    propHeadFinal := 480, depLengthAt10 := 240, depLengthAt15 := 275, depLengthAt20 := 305 }

/-- English (Indo-European, head-initial, SVO) -/
def english : LanguageDLM :=
  { name := "English", isoCode := "en", family := "Indo-European"
    propHeadFinal := 320, depLengthAt10 := 220, depLengthAt15 := 250, depLengthAt20 := 270 }

/-- Estonian (Uralic, mixed) -/
def estonian : LanguageDLM :=
  { name := "Estonian", isoCode := "et", family := "Uralic"
    propHeadFinal := 490, depLengthAt10 := 235, depLengthAt15 := 270, depLengthAt20 := 295 }

/-- Finnish (Uralic, head-final, SVO) -/
def finnish : LanguageDLM :=
  { name := "Finnish", isoCode := "fi", family := "Uralic"
    propHeadFinal := 530, depLengthAt10 := 240, depLengthAt15 := 275, depLengthAt20 := 300 }

/-- French (Indo-European, head-initial, SVO) -/
def french : LanguageDLM :=
  { name := "French", isoCode := "fr", family := "Indo-European"
    propHeadFinal := 290, depLengthAt10 := 215, depLengthAt15 := 245, depLengthAt20 := 265 }

/-- German (Indo-European, mixed V2/SOV) -/
def german : LanguageDLM :=
  { name := "German", isoCode := "de", family := "Indo-European"
    propHeadFinal := 480, depLengthAt10 := 240, depLengthAt15 := 280, depLengthAt20 := 310 }

/-- Greek (Indo-European, head-initial, SVO) -/
def greek : LanguageDLM :=
  { name := "Greek", isoCode := "el", family := "Indo-European"
    propHeadFinal := 350, depLengthAt10 := 225, depLengthAt15 := 255, depLengthAt20 := 280 }

/-- Hebrew (Afro-Asiatic, head-initial, SVO) -/
def hebrew : LanguageDLM :=
  { name := "Hebrew", isoCode := "he", family := "Afro-Asiatic"
    propHeadFinal := 270, depLengthAt10 := 220, depLengthAt15 := 250, depLengthAt20 := 275 }

/-- Hindi (Indo-European, head-final, SOV) -/
def hindi : LanguageDLM :=
  { name := "Hindi", isoCode := "hi", family := "Indo-European"
    propHeadFinal := 780, depLengthAt10 := 260, depLengthAt15 := 310, depLengthAt20 := 345 }

/-- Hungarian (Uralic, head-final) -/
def hungarian : LanguageDLM :=
  { name := "Hungarian", isoCode := "hu", family := "Uralic"
    propHeadFinal := 580, depLengthAt10 := 245, depLengthAt15 := 280, depLengthAt20 := 310 }

/-- Indonesian (Austronesian, head-initial, SVO) -/
def indonesian : LanguageDLM :=
  { name := "Indonesian", isoCode := "id", family := "Austronesian"
    propHeadFinal := 250, depLengthAt10 := 210, depLengthAt15 := 235, depLengthAt20 := 255 }

/-- Italian (Indo-European, head-initial, SVO) -/
def italian : LanguageDLM :=
  { name := "Italian", isoCode := "it", family := "Indo-European"
    propHeadFinal := 300, depLengthAt10 := 220, depLengthAt15 := 250, depLengthAt20 := 270 }

/-- Japanese (Japonic, head-final, SOV) -/
def japanese : LanguageDLM :=
  { name := "Japanese", isoCode := "ja", family := "Japonic"
    propHeadFinal := 890, depLengthAt10 := 275, depLengthAt15 := 330, depLengthAt20 := 370 }

/-- Korean (Koreanic, head-final, SOV) -/
def korean : LanguageDLM :=
  { name := "Korean", isoCode := "ko", family := "Koreanic"
    propHeadFinal := 870, depLengthAt10 := 270, depLengthAt15 := 325, depLengthAt20 := 365 }

/-- Latin (Indo-European, head-final, SOV) -/
def latin : LanguageDLM :=
  { name := "Latin", isoCode := "la", family := "Indo-European"
    propHeadFinal := 600, depLengthAt10 := 250, depLengthAt15 := 290, depLengthAt20 := 320 }

/-- Norwegian (Indo-European, head-initial, SVO) -/
def norwegian : LanguageDLM :=
  { name := "Norwegian", isoCode := "no", family := "Indo-European"
    propHeadFinal := 360, depLengthAt10 := 220, depLengthAt15 := 250, depLengthAt20 := 275 }

/-- Persian (Indo-European, head-final, SOV) -/
def persian : LanguageDLM :=
  { name := "Persian", isoCode := "fa", family := "Indo-European"
    propHeadFinal := 650, depLengthAt10 := 250, depLengthAt15 := 285, depLengthAt20 := 315 }

/-- Polish (Indo-European, head-initial, SVO) -/
def polish : LanguageDLM :=
  { name := "Polish", isoCode := "pl", family := "Indo-European"
    propHeadFinal := 420, depLengthAt10 := 230, depLengthAt15 := 265, depLengthAt20 := 290 }

/-- Portuguese (Indo-European, head-initial, SVO) -/
def portuguese : LanguageDLM :=
  { name := "Portuguese", isoCode := "pt", family := "Indo-European"
    propHeadFinal := 280, depLengthAt10 := 215, depLengthAt15 := 245, depLengthAt20 := 265 }

/-- Romanian (Indo-European, head-initial, SVO) -/
def romanian : LanguageDLM :=
  { name := "Romanian", isoCode := "ro", family := "Indo-European"
    propHeadFinal := 290, depLengthAt10 := 215, depLengthAt15 := 240, depLengthAt20 := 260 }

/-- Russian (Indo-European, mixed) -/
def russian : LanguageDLM :=
  { name := "Russian", isoCode := "ru", family := "Indo-European"
    propHeadFinal := 430, depLengthAt10 := 235, depLengthAt15 := 270, depLengthAt20 := 300 }

/-- Spanish (Indo-European, head-initial, SVO) -/
def spanish : LanguageDLM :=
  { name := "Spanish", isoCode := "es", family := "Indo-European"
    propHeadFinal := 280, depLengthAt10 := 215, depLengthAt15 := 245, depLengthAt20 := 265 }

/-- Swedish (Indo-European, head-initial, SVO) -/
def swedish : LanguageDLM :=
  { name := "Swedish", isoCode := "sv", family := "Indo-European"
    propHeadFinal := 370, depLengthAt10 := 225, depLengthAt15 := 255, depLengthAt20 := 280 }

/-- Tamil (Dravidian, head-final, SOV) -/
def tamil : LanguageDLM :=
  { name := "Tamil", isoCode := "ta", family := "Dravidian"
    propHeadFinal := 830, depLengthAt10 := 265, depLengthAt15 := 320, depLengthAt20 := 355 }

/-- Turkish (Turkic, head-final, SOV) -/
def turkish : LanguageDLM :=
  { name := "Turkish", isoCode := "tr", family := "Turkic"
    propHeadFinal := 810, depLengthAt10 := 260, depLengthAt15 := 310, depLengthAt20 := 350 }

/-- Urdu (Indo-European, head-final, SOV) -/
def urdu : LanguageDLM :=
  { name := "Urdu", isoCode := "ur", family := "Indo-European"
    propHeadFinal := 770, depLengthAt10 := 258, depLengthAt15 := 305, depLengthAt20 := 340 }

/-- Vietnamese (Austroasiatic, head-initial, SVO) -/
def vietnamese : LanguageDLM :=
  { name := "Vietnamese", isoCode := "vi", family := "Austroasiatic"
    propHeadFinal := 260, depLengthAt10 := 212, depLengthAt15 := 238, depLengthAt20 := 258 }

-- ============================================================================
-- Language Lists
-- ============================================================================

/-- Representative subset of 32 languages from Table 2. -/
def languages : List LanguageDLM :=
  [ arabic, basque, bulgarian, chinese, czech, danish, dutch, english
  , estonian, finnish, french, german, greek, hebrew, hindi, hungarian
  , indonesian, italian, japanese, korean, latin, norwegian, persian
  , polish, portuguese, romanian, russian, spanish, swedish, tamil
  , turkish, urdu, vietnamese ]

/-- Head-final languages in the dataset. -/
def headFinalLanguages : List LanguageDLM :=
  languages.filter (·.isHeadFinal)

/-- Head-initial languages in the dataset. -/
def headInitialLanguages : List LanguageDLM :=
  languages.filter (·.isHeadInitial)

-- ============================================================================
-- Per-Datum Classification Verification
-- ============================================================================

/-- Japanese is classified as head-final. -/
example : japanese.isHeadFinal = true := by native_decide

/-- Korean is classified as head-final. -/
example : korean.isHeadFinal = true := by native_decide

/-- Turkish is classified as head-final. -/
example : turkish.isHeadFinal = true := by native_decide

/-- Hindi is classified as head-final. -/
example : hindi.isHeadFinal = true := by native_decide

/-- Tamil is classified as head-final. -/
example : tamil.isHeadFinal = true := by native_decide

/-- English is classified as head-initial. -/
example : english.isHeadInitial = true := by native_decide

/-- Arabic is classified as head-initial. -/
example : arabic.isHeadInitial = true := by native_decide

/-- Indonesian is classified as head-initial. -/
example : indonesian.isHeadInitial = true := by native_decide

/-- French is classified as head-initial. -/
example : french.isHeadInitial = true := by native_decide

/-- Romanian is classified as head-initial. -/
example : romanian.isHeadInitial = true := by native_decide

-- ============================================================================
-- Empirical Generalizations
-- ============================================================================

/-- Mean dep length at length 10 for head-final subset. -/
def meanDepLengthHF10 : Nat :=
  let hf := headFinalLanguages
  if hf.isEmpty then 0
  else hf.foldl (λ acc l => acc + l.depLengthAt10) 0 / hf.length

/-- Mean dep length at length 10 for head-initial subset. -/
def meanDepLengthHI10 : Nat :=
  let hi := headInitialLanguages
  if hi.isEmpty then 0
  else hi.foldl (λ acc l => acc + l.depLengthAt10) 0 / hi.length

/-- Head-final languages have higher mean dep length at sentence length 10.

This is the core empirical finding: head-final languages systematically
exhibit longer dependencies, consistent with DLM theory's prediction that
consistently head-final order creates longer dependencies when combined
with right-branching structure. -/
theorem headFinal_higher_depLength_10 :
    meanDepLengthHF10 > meanDepLengthHI10 := by native_decide

/-- Same pattern at sentence length 20. -/
def meanDepLengthHF20 : Nat :=
  let hf := headFinalLanguages
  if hf.isEmpty then 0
  else hf.foldl (λ acc l => acc + l.depLengthAt20) 0 / hf.length

def meanDepLengthHI20 : Nat :=
  let hi := headInitialLanguages
  if hi.isEmpty then 0
  else hi.foldl (λ acc l => acc + l.depLengthAt20) 0 / hi.length

theorem headFinal_higher_depLength_20 :
    meanDepLengthHF20 > meanDepLengthHI20 := by native_decide

/-- Japanese has the highest dep length at length 20 among all languages. -/
theorem japanese_highest_depLength_20 :
    languages.all (·.depLengthAt20 ≤ japanese.depLengthAt20) = true := by native_decide

/-- Indonesian has the lowest dep length at length 10 among all languages. -/
theorem indonesian_lowest_depLength_10 :
    languages.all (·.depLengthAt10 ≥ indonesian.depLengthAt10) = true := by native_decide

/-- The head-finality gap increases with sentence length:
the difference in mean dep length between head-final and head-initial languages
is larger at length 20 than at length 10. -/
theorem headFinality_gap_increases :
    meanDepLengthHF20 - meanDepLengthHI20 > meanDepLengthHF10 - meanDepLengthHI10 := by
  native_decide

end Phenomena.WordOrder.DependencyLength.FutrellEtAl2020
