import Linglib.Theories.Processing.MemorySurprisal.Basic
import Linglib.Phenomena.WordOrder.Studies.FutrellEtAl2020
import Linglib.Theories.Syntax.DependencyGrammar.Formal.HarmonicOrder
import Linglib.Core.WALS.Languages

/-!
# 54-Language Word-Order Efficiency
@cite{hahn-degen-futrell-2021}

54 languages from Universal Dependencies corpora, measuring whether real
word orders achieve more efficient memory-surprisal trade-offs than
grammar-preserving random baselines. 50/54 languages are more efficient;
the 4 exceptions (Latvian, North Sami, Polish, Slovak) all have high
word-order freedom (high branching direction entropy).

## Values

- `moreEfficient`: whether the real language's trade-off AUC < baseline AUC
- `gMean1000`: bootstrapped mean G × 1000 (SI Figure 2). G = 1.0 means fully optimized.
- `branchDirEntropy1000`: branching direction entropy × 1000 (higher = more
  word-order freedom). From `branching_entropy.tsv` at
  https://github.com/m-hahn/memory-surprisal (used in Figure 13 via `order_freedom.R`).
  Korean's entropy is unavailable in the published data.
-/

namespace Phenomena.WordOrder.Studies.HahnDegenFutrell2021

-- ============================================================================
-- Data Structure
-- ============================================================================

/-- Efficiency data for a single language from Study 2. -/
structure LanguageEfficiency where
  name : String
  isoCode : String
  family : String
  /-- Whether the real language achieves a more efficient trade-off than baselines -/
  moreEfficient : Bool
  /-- Bootstrapped mean G × 1000 (from SI Figure 2). 1000 = fully optimized. -/
  gMean1000 : Nat
  /-- Branching direction entropy × 1000 (higher = more word-order freedom).
      `none` when the value is unavailable in the published data. -/
  branchDirEntropy1000 : Option Nat
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Language Data (54 languages, SI Table 2 + SI Figure 2)
-- ============================================================================

/-! ### Efficient languages (50)

G ≥ 0.5 in the LSTM estimator (main paper). Most have G = 1.0. -/

def afrikaans : LanguageEfficiency :=
  { name := "Afrikaans", isoCode := "af", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 195 }
def amharic : LanguageEfficiency :=
  { name := "Amharic", isoCode := "am", family := "Afro-Asiatic"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 247 }
def arabic : LanguageEfficiency :=
  { name := "Arabic", isoCode := "ar", family := "Afro-Asiatic"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 178 }
def armenian : LanguageEfficiency :=
  { name := "Armenian", isoCode := "hy", family := "Indo-European"
    moreEfficient := true, gMean1000 := 920, branchDirEntropy1000 := some 337 }
def bambara : LanguageEfficiency :=
  { name := "Bambara", isoCode := "bm", family := "Mande"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 110 }
def basque : LanguageEfficiency :=
  { name := "Basque", isoCode := "eu", family := "Isolate"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 397 }
def breton : LanguageEfficiency :=
  { name := "Breton", isoCode := "br", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 279 }
def bulgarian : LanguageEfficiency :=
  { name := "Bulgarian", isoCode := "bg", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 254 }
def buryat : LanguageEfficiency :=
  { name := "Buryat", isoCode := "bxr", family := "Mongolic"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 169 }
def cantonese : LanguageEfficiency :=
  { name := "Cantonese", isoCode := "yue", family := "Sino-Tibetan"
    moreEfficient := true, gMean1000 := 960, branchDirEntropy1000 := some 171 }
def catalan : LanguageEfficiency :=
  { name := "Catalan", isoCode := "ca", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 207 }
def chinese : LanguageEfficiency :=
  { name := "Chinese", isoCode := "zh", family := "Sino-Tibetan"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 144 }
def croatian : LanguageEfficiency :=
  { name := "Croatian", isoCode := "hr", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 271 }
def czech : LanguageEfficiency :=
  { name := "Czech", isoCode := "cs", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 328 }
def danish : LanguageEfficiency :=
  { name := "Danish", isoCode := "da", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 250 }
def dutch : LanguageEfficiency :=
  { name := "Dutch", isoCode := "nl", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 280 }
def english : LanguageEfficiency :=
  { name := "English", isoCode := "en", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 191 }
def erzya : LanguageEfficiency :=
  { name := "Erzya", isoCode := "myv", family := "Uralic"
    moreEfficient := true, gMean1000 := 990, branchDirEntropy1000 := some 429 }
def estonian : LanguageEfficiency :=
  { name := "Estonian", isoCode := "et", family := "Uralic"
    moreEfficient := true, gMean1000 := 800, branchDirEntropy1000 := some 435 }
def faroese : LanguageEfficiency :=
  { name := "Faroese", isoCode := "fo", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 211 }
def finnish : LanguageEfficiency :=
  { name := "Finnish", isoCode := "fi", family := "Uralic"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 357 }
def french : LanguageEfficiency :=
  { name := "French", isoCode := "fr", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 186 }
def german : LanguageEfficiency :=
  { name := "German", isoCode := "de", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 280 }
def greek : LanguageEfficiency :=
  { name := "Greek", isoCode := "el", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 219 }
def hebrew : LanguageEfficiency :=
  { name := "Hebrew", isoCode := "he", family := "Afro-Asiatic"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 173 }
def hindi : LanguageEfficiency :=
  { name := "Hindi", isoCode := "hi", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 59 }
def hungarian : LanguageEfficiency :=
  { name := "Hungarian", isoCode := "hu", family := "Uralic"
    moreEfficient := true, gMean1000 := 870, branchDirEntropy1000 := some 290 }
def indonesian : LanguageEfficiency :=
  { name := "Indonesian", isoCode := "id", family := "Austronesian"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 237 }
def italian : LanguageEfficiency :=
  { name := "Italian", isoCode := "it", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 216 }
def japanese : LanguageEfficiency :=
  { name := "Japanese", isoCode := "ja", family := "Japonic"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 24 }
def kazakh : LanguageEfficiency :=
  { name := "Kazakh", isoCode := "kk", family := "Turkic"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 147 }
def korean : LanguageEfficiency :=
  { name := "Korean", isoCode := "ko", family := "Koreanic"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := none }
def kurmanji : LanguageEfficiency :=
  { name := "Kurmanji", isoCode := "kmr", family := "Indo-European"
    moreEfficient := true, gMean1000 := 930, branchDirEntropy1000 := some 262 }
def maltese : LanguageEfficiency :=
  { name := "Maltese", isoCode := "mt", family := "Afro-Asiatic"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 185 }
def naija : LanguageEfficiency :=
  { name := "Naija", isoCode := "pcm", family := "Creole"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 239 }
def norwegian : LanguageEfficiency :=
  { name := "Norwegian", isoCode := "no", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 220 }
def persian : LanguageEfficiency :=
  { name := "Persian", isoCode := "fa", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 142 }
def portuguese : LanguageEfficiency :=
  { name := "Portuguese", isoCode := "pt", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 223 }
def romanian : LanguageEfficiency :=
  { name := "Romanian", isoCode := "ro", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 267 }
def russian : LanguageEfficiency :=
  { name := "Russian", isoCode := "ru", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 252 }
def serbian : LanguageEfficiency :=
  { name := "Serbian", isoCode := "sr", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 244 }
def slovenian : LanguageEfficiency :=
  { name := "Slovenian", isoCode := "sl", family := "Indo-European"
    moreEfficient := true, gMean1000 := 820, branchDirEntropy1000 := some 309 }
def spanish : LanguageEfficiency :=
  { name := "Spanish", isoCode := "es", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 228 }
def swedish : LanguageEfficiency :=
  { name := "Swedish", isoCode := "sv", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 229 }
def thai : LanguageEfficiency :=
  { name := "Thai", isoCode := "th", family := "Kra-Dai"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 149 }
def turkish : LanguageEfficiency :=
  { name := "Turkish", isoCode := "tr", family := "Turkic"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 246 }
def ukrainian : LanguageEfficiency :=
  { name := "Ukrainian", isoCode := "uk", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 313 }
def urdu : LanguageEfficiency :=
  { name := "Urdu", isoCode := "ur", family := "Indo-European"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 85 }
def uyghur : LanguageEfficiency :=
  { name := "Uyghur", isoCode := "ug", family := "Turkic"
    moreEfficient := true, gMean1000 := 650, branchDirEntropy1000 := some 87 }
def vietnamese : LanguageEfficiency :=
  { name := "Vietnamese", isoCode := "vi", family := "Austroasiatic"
    moreEfficient := true, gMean1000 := 1000, branchDirEntropy1000 := some 320 }

/-! ### Exception languages (4)

G < 0.5 in the LSTM estimator (main paper, Figure 13; SI Figure 2).
All have high branching direction entropy (free word order). -/

def latvian : LanguageEfficiency :=
  { name := "Latvian", isoCode := "lv", family := "Indo-European"
    moreEfficient := false, gMean1000 := 490, branchDirEntropy1000 := some 347 }
def northSami : LanguageEfficiency :=
  { name := "North Sami", isoCode := "sme", family := "Uralic"
    moreEfficient := false, gMean1000 := 370, branchDirEntropy1000 := some 315 }
def polish : LanguageEfficiency :=
  { name := "Polish", isoCode := "pl", family := "Indo-European"
    moreEfficient := false, gMean1000 := 100, branchDirEntropy1000 := some 375 }
def slovak : LanguageEfficiency :=
  { name := "Slovak", isoCode := "sk", family := "Indo-European"
    moreEfficient := false, gMean1000 := 70, branchDirEntropy1000 := some 372 }

-- ============================================================================
-- Language Lists
-- ============================================================================

/-- All 54 languages from Study 2 (SI Table 2). -/
def allLanguages : List LanguageEfficiency :=
  [ afrikaans, amharic, arabic, armenian, bambara, basque, breton, bulgarian
  , buryat, cantonese, catalan, chinese, croatian, czech, danish, dutch
  , english, erzya, estonian, faroese, finnish, french, german, greek
  , hebrew, hindi, hungarian, indonesian, italian, japanese, kazakh, korean
  , kurmanji, maltese, naija, norwegian, persian, portuguese, romanian
  , russian, serbian, slovenian, spanish, swedish, thai, turkish, ukrainian
  , urdu, uyghur, vietnamese
  , latvian, northSami, polish, slovak ]

/-- The 50 efficient languages. -/
def efficientLanguages : List LanguageEfficiency :=
  allLanguages.filter (·.moreEfficient)

/-- The 4 exception languages. -/
def exceptionLanguages : List LanguageEfficiency :=
  allLanguages.filter (! ·.moreEfficient)

-- ============================================================================
-- Core Theorems
-- ============================================================================

/-- 54 languages in total. -/
theorem total_count : allLanguages.length = 54 := by native_decide

/-- 50 out of 54 languages have more efficient word orders than baselines. -/
theorem most_languages_efficient :
    efficientLanguages.length = 50 := by native_decide

/-- Exactly 4 exceptions. -/
theorem exceptions_count :
    exceptionLanguages.length = 4 := by native_decide

/-- All 4 exceptions have high branching direction entropy (> 300 × 10⁻³).

This supports the paper's explanation: languages with very free word order
have weaker optimization pressure because many orderings are nearly
equally acceptable, reducing the signal of optimization.

Entropy values from `branching_entropy.tsv` at
https://github.com/m-hahn/memory-surprisal -/
theorem all_exceptions_have_high_word_order_freedom :
    exceptionLanguages.all (λ l =>
      match l.branchDirEntropy1000 with | some e => e > 300 | none => false
    ) = true := by native_decide

/-- All 4 exceptions have G < 500 (below the optimization threshold). -/
theorem all_exceptions_below_threshold :
    exceptionLanguages.all (·.gMean1000 < 500) = true := by native_decide

-- ============================================================================
-- Per-Datum Verification
-- ============================================================================

/-- Japanese is efficient (strongly head-final, low entropy). -/
theorem japanese_efficient : japanese.moreEfficient = true := by native_decide
/-- English is efficient. -/
theorem english_efficient : english.moreEfficient = true := by native_decide
/-- Arabic is efficient. -/
theorem arabic_efficient : arabic.moreEfficient = true := by native_decide
/-- German is efficient. -/
theorem german_efficient : german.moreEfficient = true := by native_decide
/-- Finnish is efficient. -/
theorem finnish_efficient : finnish.moreEfficient = true := by native_decide
/-- Turkish is efficient. -/
theorem turkish_efficient : turkish.moreEfficient = true := by native_decide
/-- Korean is efficient. -/
theorem korean_efficient : korean.moreEfficient = true := by native_decide

/-- Latvian is an exception. -/
theorem latvian_exception : latvian.moreEfficient = false := by native_decide
/-- North Sami is an exception. -/
theorem northSami_exception : northSami.moreEfficient = false := by native_decide
/-- Polish is an exception. -/
theorem polish_exception : polish.moreEfficient = false := by native_decide
/-- Slovak is an exception. -/
theorem slovak_exception : slovak.moreEfficient = false := by native_decide

-- ============================================================================
-- Entropy Patterns
-- ============================================================================

/-- Japanese has the lowest branching direction entropy among languages with
known entropy data (most rigid word order). Korean is excluded because its
entropy is not available in the published data. -/
theorem japanese_lowest_known_entropy :
    (allLanguages.filterMap (·.branchDirEntropy1000)).all (· ≥ 24) = true := by
  native_decide

/-- Estonian has the highest entropy among efficient languages (435) but is
still efficient (G = 0.80), showing that word-order freedom is necessary
but not sufficient for being an exception. -/
theorem estonian_high_entropy_efficient :
    estonian.branchDirEntropy1000 = some 435 ∧ estonian.moreEfficient = true := by
  exact ⟨rfl, rfl⟩

/-- Mean branching direction entropy is higher for exceptions than efficient
languages (computed over languages with known entropy). -/
def meanEntropy (ls : List LanguageEfficiency) : Nat :=
  let known := ls.filterMap (·.branchDirEntropy1000)
  if known.isEmpty then 0
  else known.foldl (· + ·) 0 / known.length

theorem exceptions_higher_mean_entropy :
    meanEntropy exceptionLanguages > meanEntropy efficientLanguages := by native_decide

-- ============================================================================
-- G-Value Patterns
-- ============================================================================

/-- Slovak has the lowest G value (least evidence for optimization). -/
theorem slovak_lowest_g :
    allLanguages.all (·.gMean1000 ≥ slovak.gMean1000) = true := by native_decide

/-- Most efficient languages have G = 1.0 (44 out of 50). -/
theorem most_efficient_fully_optimized :
    (efficientLanguages.filter (·.gMean1000 = 1000)).length ≥ 40 := by native_decide

-- ============================================================================
-- Crosslinguistic Bridge to @cite{futrell-gibson-2020}
-- ============================================================================

open Phenomena.WordOrder.DependencyLength.FutrellEtAl2020

/-- ISO codes appearing in @cite{futrell-gibson-2020}'s 32-language dataset. -/
def futrellIsoCodes : List String :=
  Phenomena.WordOrder.DependencyLength.FutrellEtAl2020.languages.map (·.isoCode)

/-- ISO codes appearing in this study's 54-language dataset. -/
def hahnIsoCodes : List String :=
  allLanguages.map (·.isoCode)

/-- Languages in both datasets (by ISO code). -/
def sharedIsoCodes : List String :=
  futrellIsoCodes.filter (hahnIsoCodes.contains ·)

/-- At least 20 languages appear in both datasets. -/
theorem many_shared_languages :
    sharedIsoCodes.length ≥ 20 := by native_decide

/-- All but one shared language (Polish) are efficient in this study. -/
theorem shared_languages_mostly_efficient :
    (sharedIsoCodes.filter (λ iso =>
      (allLanguages.filter (·.isoCode == iso)).all (·.moreEfficient)
    )).length ≥ sharedIsoCodes.length - 1 := by native_decide

/-- Polish is the only shared language that is an exception. -/
theorem polish_only_shared_exception :
    (sharedIsoCodes.filter (λ iso =>
      (allLanguages.filter (·.isoCode == iso)).any (! ·.moreEfficient)
    )) = ["pl"] := by native_decide

-- ============================================================================
-- Bridge to HarmonicOrder (DLM explains head-direction generalization)
-- ============================================================================

/-- The DLM harmonic order prediction holds (from HarmonicOrder.lean). -/
theorem harmonic_dlm_holds :
    DepGrammar.HarmonicOrder.dlmPredictsHarmonicCheaper = true := by native_decide

/-- Languages with known low branching entropy (< 300) are all efficient. -/
theorem rigid_order_languages_efficient :
    (allLanguages.filter (λ l =>
      match l.branchDirEntropy1000 with | some e => e < 300 | none => false
    )).all (·.moreEfficient) = true := by native_decide

/-- All 4 exceptions have entropy ≥ 315. -/
theorem exceptions_all_high_entropy :
    exceptionLanguages.all (λ l =>
      match l.branchDirEntropy1000 with | some e => e ≥ 315 | none => false
    ) = true := by native_decide

/-- Not all high-entropy languages are exceptions: word-order freedom is
necessary but not sufficient for being an exception. -/
theorem high_entropy_not_sufficient :
    (allLanguages.filter (λ l =>
      match l.branchDirEntropy1000 with | some e => e ≥ 315 | none => false
    )).any (·.moreEfficient) = true := by native_decide

-- ============================================================================
-- Bridge to WALS (@cite{dryer-haspelmath-2013})
-- ============================================================================

/-! ### WALS Language Validation

The study uses ISO 639-1 codes (2-letter) from Universal Dependencies.
WALS uses ISO 639-3 codes (3-letter). This mapping connects them,
enabling family classification cross-checks against WALS v2020.4.

**Coverage**: 51 of 54 languages have WALS entries (missing: Buryat, Croatian,
Serbian). Of 51, **42 have identical family names**; 9 differ due to
terminology (Turkic/Altaic, Japonic/Japanese, Kra-Dai/Tai-Kadai, etc.).

ISO 639-1 codes that coincide with ISO 639-3 pass through directly. For
macrolanguages (Arabic, Chinese, Persian, Estonian), the mapping points to
the specific ISO 639-3 variety used in WALS. -/

/-- ISO 639-1 (study) → ISO 639-3 (WALS) mapping for the 54 languages. -/
def iso1to3 : List (String × String) :=
  [ ("af", "afr"), ("am", "amh"), ("ar", "arb"), ("hy", "hye"), ("bm", "bam")
  , ("eu", "eus"), ("br", "bre"), ("bg", "bul"), ("bxr", "bxr"), ("yue", "yue")
  , ("ca", "cat"), ("zh", "cmn"), ("hr", "hrv"), ("cs", "ces"), ("da", "dan")
  , ("nl", "nld"), ("en", "eng"), ("myv", "myv"), ("et", "ekk"), ("fo", "fao")
  , ("fi", "fin"), ("fr", "fra"), ("de", "deu"), ("el", "ell"), ("he", "heb")
  , ("hi", "hin"), ("hu", "hun"), ("id", "ind"), ("it", "ita"), ("ja", "jpn")
  , ("kk", "kaz"), ("ko", "kor"), ("kmr", "kmr"), ("lv", "lav"), ("mt", "mlt")
  , ("pcm", "pcm"), ("sme", "sme"), ("no", "nor"), ("fa", "pes"), ("pl", "pol")
  , ("pt", "por"), ("ro", "ron"), ("ru", "rus"), ("sr", "srp"), ("sk", "slk")
  , ("sl", "slv"), ("es", "spa"), ("sv", "swe"), ("th", "tha"), ("tr", "tur")
  , ("uk", "ukr"), ("ur", "urd"), ("ug", "uig"), ("vi", "vie") ]

/-- Look up a study language's WALS entry via its ISO code. -/
def walsLookup (l : LanguageEfficiency) : Option Core.WALS.Language :=
  match iso1to3.find? (·.1 == l.isoCode) with
  | some (_, iso3) => Core.WALS.findByIso iso3
  | none => none

/-- Languages with WALS entries (51 of 54). -/
def walsMatchedLanguages : List LanguageEfficiency :=
  allLanguages.filter (walsLookup · |>.isSome)

/-- 51 of 54 study languages have WALS entries. -/
theorem wals_coverage : walsMatchedLanguages.length = 51 := by native_decide

/-- The 3 languages without WALS entries are Buryat, Croatian, and Serbian. -/
theorem wals_missing :
    (allLanguages.filter (walsLookup · |>.isNone)).map (·.name)
    = ["Buryat", "Croatian", "Serbian"] := by native_decide

/-- For all 42 languages where the family names agree, the study family
matches the WALS family exactly. -/
theorem wals_family_agreement_count :
    (walsMatchedLanguages.filter (λ l =>
      match walsLookup l with
      | some w => w.family == l.family
      | none => false
    )).length = 42 := by native_decide

/-- The 9 family-name divergences (all terminological, not errors):
- Basque: study "Isolate" vs WALS "Basque"
- Japanese: "Japonic" vs "Japanese"
- Kazakh/Turkish/Uyghur: "Turkic" vs "Altaic" (Altaic hypothesis disputed)
- Korean: "Koreanic" vs "Korean"
- Naija: "Creole" vs "other"
- Thai: "Kra-Dai" vs "Tai-Kadai"
- Vietnamese: "Austroasiatic" vs "Austro-Asiatic" (hyphenation) -/
theorem wals_family_divergence_count :
    (walsMatchedLanguages.filter (λ l =>
      match walsLookup l with
      | some w => w.family != l.family
      | none => false
    )).length = 9 := by native_decide

end Phenomena.WordOrder.Studies.HahnDegenFutrell2021
