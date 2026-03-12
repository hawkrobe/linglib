import Linglib.Theories.Processing.MemorySurprisal.Basic
import Linglib.Phenomena.WordOrder.Studies.FutrellEtAl2020
import Linglib.Theories.Syntax.DependencyGrammar.Formal.HarmonicOrder
import Linglib.Core.WALS.Languages

/-!
# Study 2: 54-Language Word-Order Efficiency
@cite{hahn-degen-futrell-2021}

Tests the **Efficient Trade-off Hypothesis**: the ordering regularities
of natural language optimize the memory-surprisal trade-off, serving the
communicative interest of the hearer. 54 languages from Universal
Dependencies corpora are measured against grammar-preserving random
baselines. 50/54 languages have significantly more efficient trade-offs;
the 4 exceptions (Latvian, North Sami, Polish, Slovak) all have high
word-order freedom (high branching direction entropy).

Key empirical finding (Figure 13): branching direction entropy is
**negatively correlated** with optimization strength (Spearman ρ ≈ −.58,
p < .0001). Languages with freer word order show weaker optimization,
plausibly because free-order languages use word order to encode
information structure rather than minimize processing cost.

## Values

- `moreEfficient`: whether the real language's trade-off AUC is
  significantly lower than baseline AUCs (two-sided binomial test,
  Hochberg-corrected p < .01)
- `gMean1000`: bootstrapped mean G × 1000 (SI Figure 2). G = fraction of
  baseline grammars less efficient than the real language. 1000 = fully
  optimized.
- `branchDirEntropy1000`: branching direction entropy × 1000 (higher = more
  word-order freedom). From `branching_entropy.tsv` at
  https://github.com/m-hahn/memory-surprisal (used in Figure 13 via `order_freedom.R`).
  Korean's entropy is unavailable in the published data.
-/

namespace Phenomena.WordOrder.Studies.HahnDegenFutrell2021

open Processing.MemorySurprisal

-- ============================================================================
-- Data Structure
-- ============================================================================

/-- Efficiency data for a single language from Study 2. -/
structure LanguageEfficiency where
  name : String
  isoCode : String
  family : String
  /-- Whether the real language's trade-off AUC is significantly lower than
  baseline AUCs (Hochberg-corrected p < .01). This is the empirical
  instantiation of `Processing.MemorySurprisal.efficientTradeoffHypothesis`
  from the theory module. -/
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
-- Cross-Field Consistency
-- ============================================================================

/-- The `moreEfficient` flag is consistent with a G ≥ 500 threshold
across all 54 languages. This cross-checks two independently encoded
fields: `moreEfficient` (from the binomial test) and `gMean1000`
(from SI Figure 2's bootstrapped fraction). -/
theorem efficiency_consistent_with_g_threshold :
    allLanguages.all (λ l => l.moreEfficient == (l.gMean1000 ≥ 500)) = true := by
  native_decide

/-- The 4 exceptions form a contiguous block at the bottom of the G
ranking: no efficient language has G below any exception's G. -/
theorem exceptions_below_all_efficient :
    exceptionLanguages.all (λ exc =>
      efficientLanguages.all (λ eff => eff.gMean1000 > exc.gMean1000)
    ) = true := by native_decide

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

/-- 42 out of 50 efficient languages have G = 1.0 (fully optimized:
the real language beats every sampled baseline grammar). -/
theorem most_efficient_fully_optimized :
    (efficientLanguages.filter (·.gMean1000 = 1000)).length = 42 := by native_decide

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
-- Entropy–Optimization Correlation (Figure 13)
-- ============================================================================

/-! ### Negative correlation between word-order freedom and optimization

Figure 13 of @cite{hahn-degen-futrell-2021} shows that branching direction
entropy (x-axis) is negatively correlated with the surprisal difference
between real and baseline orders (y-axis). Spearman ρ ≈ −.58, p < .0001.

We cannot compute a Spearman correlation in Lean without a ranking function,
but we can verify the key structural claims that drive the correlation:
- All low-entropy languages are efficient (rigid order → strong optimization)
- All exceptions have high entropy (free order → weak optimization)
- High entropy is necessary but not sufficient for being an exception -/

/-- Languages with known low branching entropy (< 300) are all efficient.
This is the left side of Figure 13: rigid-order languages cluster at
high surprisal difference (strong optimization). -/
theorem rigid_order_languages_efficient :
    (allLanguages.filter (λ l =>
      match l.branchDirEntropy1000 with | some e => e < 300 | none => false
    )).all (·.moreEfficient) = true := by native_decide

/-- All 4 exceptions have entropy ≥ 315.
This is the lower-right of Figure 13: exceptions cluster at high entropy. -/
theorem exceptions_all_high_entropy :
    exceptionLanguages.all (λ l =>
      match l.branchDirEntropy1000 with | some e => e ≥ 315 | none => false
    ) = true := by native_decide

/-- Not all high-entropy languages are exceptions: word-order freedom is
necessary but not sufficient for being an exception. Estonian (entropy 435)
and Finnish (357) are efficient despite high entropy. -/
theorem high_entropy_not_sufficient :
    (allLanguages.filter (λ l =>
      match l.branchDirEntropy1000 with | some e => e ≥ 315 | none => false
    )).any (·.moreEfficient) = true := by native_decide

/-- The mean G value decreases as entropy increases: partition languages
into low-entropy (< 250) and high-entropy (≥ 250) groups. The low-entropy
group has higher mean G, consistent with the negative correlation. -/
theorem low_entropy_higher_mean_g :
    let lowEntropy := allLanguages.filter (λ l =>
      match l.branchDirEntropy1000 with | some e => e < 250 | none => false)
    let highEntropy := allLanguages.filter (λ l =>
      match l.branchDirEntropy1000 with | some e => e ≥ 250 | none => false)
    (lowEntropy.map (·.gMean1000)).foldl (· + ·) 0 / lowEntropy.length >
    (highEntropy.map (·.gMean1000)).foldl (· + ·) 0 / highEntropy.length := by
  native_decide

-- ============================================================================
-- Bridge to Information Locality and DLM
-- ============================================================================

/-! ### Information locality generalizes dependency locality

@cite{hahn-degen-futrell-2021} argue (§"Other Kinds of Memory Bottlenecks"
and Discussion) that information locality generalizes dependency length
minimization: DLM minimizes *structural* distance between related words,
while information locality minimizes the *information-theoretic* distance
at which predictive information concentrates.

The HarmonicOrder module proves that consistent head direction achieves
shorter dependency chains (`harmonic_always_shorter`). The present study
shows that languages with shorter dependencies (lower branching entropy,
more consistent direction) achieve better memory-surprisal trade-offs
(`rigid_order_languages_efficient`). Together, these two results establish
the chain: harmonic order → short dependencies → information locality
→ efficient trade-off. -/

/-- The DLM harmonic order prediction holds: consistent head direction
produces shorter total dependency length (from HarmonicOrder.lean). -/
theorem harmonic_dlm_holds :
    DepGrammar.HarmonicOrder.dlmPredictsHarmonicCheaper = true := by native_decide

/-- The full chain: all languages with low entropy (consistent direction,
short dependencies) are efficient, and the DLM prediction holds.
This connects the structural argument (HarmonicOrder) to the
information-theoretic result (memory-surprisal efficiency). -/
theorem dlm_to_efficiency_chain :
    DepGrammar.HarmonicOrder.dlmPredictsHarmonicCheaper = true ∧
    (allLanguages.filter (λ l =>
      match l.branchDirEntropy1000 with | some e => e < 300 | none => false
    )).all (·.moreEfficient) = true := by
  exact ⟨by native_decide, by native_decide⟩

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
