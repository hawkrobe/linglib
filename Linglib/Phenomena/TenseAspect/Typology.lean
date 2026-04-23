import Linglib.Core.Lexical.Word
import Linglib.Datasets.WALS.Features.F65A
import Linglib.Datasets.WALS.Features.F66A
import Linglib.Datasets.WALS.Features.F67A
import Linglib.Datasets.WALS.Features.F68A
import Linglib.Datasets.WALS.Features.F69A

/-!
# Cross-Linguistic Typology of Tense and Aspect (WALS Chapters 65--69)
 @cite{comrie-1985} @cite{dryer-haspelmath-2013} @cite{dahl-velupillai-2013} @cite{de-haan-2013}

Cross-linguistic data on tense-aspect systems from the World Atlas of Language
Structures (WALS), covering five parameters:

- **Ch 65 (Perfective/Imperfective Aspect)**: Whether a language grammaticalizes
  the perfective/imperfective distinction. 222 languages, two values.

- **Ch 66 (The Past Tense)**: Whether a language has grammatical marking of
  past tense, and if so how many remoteness distinctions it makes. 222 languages,
  four values.

- **Ch 67 (The Future Tense)**: Whether a language has inflectional marking of
  future tense. 222 languages, two values.

- **Ch 68 (The Perfect)**: Whether a language has a distinct perfect category
  (resultative + experiential uses), and its diachronic source. 222 languages,
  four values.

- **Ch 69 (Position of Tense-Aspect Affixes)**: How tense-aspect is
  morphologically expressed. 1062 languages, five values.

## Key findings

@cite{dahl-velupillai-2013} @cite{bybee-perkins-pagliuca-1994} note that there is no evidence for a typological
division into "tense languages" vs "aspect languages" -- languages that have
aspectual marking tend also to have tense marking. Suffixing is overwhelmingly
the dominant strategy for tense-aspect morphology. South-East
Asian languages consistently lack morphological tense-aspect marking.

-/

namespace Phenomena.TenseAspect.Typology

-- ============================================================================
-- WALS Data Abbreviations
-- ============================================================================

private abbrev ch65 := Datasets.WALS.F65A.allData
private abbrev ch66 := Datasets.WALS.F66A.allData
private abbrev ch67 := Datasets.WALS.F67A.allData
private abbrev ch68 := Datasets.WALS.F68A.allData
private abbrev ch69 := Datasets.WALS.F69A.allData

-- ============================================================================
-- Types: WALS Chapter 65 — Perfective/Imperfective Aspect
-- ============================================================================

/-- WALS Ch 65: Whether the perfective/imperfective distinction is
    grammaticalized in the language. "Grammatical marking" includes both
    morphological and periphrastic constructions. -/
inductive AspectMarking where
  /-- Language has grammatical marking of perfective/imperfective -/
  | grammatical
  /-- Language has no grammatical marking of perfective/imperfective -/
  | none
  deriving DecidableEq, Repr

-- ============================================================================
-- Types: WALS Chapter 66 — The Past Tense
-- ============================================================================

/-- WALS Ch 66: Past tense marking and remoteness distinctions.

    Past marking includes both inflectional and periphrastic constructions.
    Past imperfectives (restricted to imperfective contexts, as in the
    Armenian Imperfect) count as past marking. -/
inductive PastMarking where
  /-- Past/non-past distinction marked, no remoteness distinctions -/
  | marked
  /-- Past/non-past distinction marked, 2-3 degrees of remoteness -/
  | markedRemoteness2_3
  /-- Past/non-past distinction marked, 4+ degrees of remoteness -/
  | markedRemoteness4plus
  /-- No grammatical marking of past/non-past distinction -/
  | none
  deriving DecidableEq, Repr

/-- Whether a language has any past tense marking (any of the three
    marked categories). -/
def PastMarking.hasMarking : PastMarking → Bool
  | .marked | .markedRemoteness2_3 | .markedRemoteness4plus => true
  | .none => false

-- ============================================================================
-- Types: WALS Chapter 67 — The Future Tense
-- ============================================================================

/-- WALS Ch 67: Whether the language has inflectional future marking.

    Only inflectional marking is counted here (not periphrastic
    constructions like English "will" + V). Irrealis markers that
    obligatorily encode future reference are included. -/
inductive FutureMarking where
  /-- Inflectional marking of future/nonfuture distinction -/
  | inflectional
  /-- No inflectional marking of future/nonfuture distinction -/
  | none
  deriving DecidableEq, Repr

-- ============================================================================
-- Types: WALS Chapter 68 — The Perfect
-- ============================================================================

/-- WALS Ch 68: Whether the language has a distinct perfect category,
    and its diachronic source.

    A form counts as a perfect only if it has both resultative and
    experiential uses (not a general past, not a dedicated resultative). -/
inductive PerfectType where
  /-- Perfect derived from possessive construction ('have'-perfect).
      Restricted almost exclusively to western Europe. -/
  | fromPossessive
  /-- Perfect derived from word meaning 'finish' or 'already'.
      Concentrated in South-East Asia and West Africa. -/
  | fromFinishAlready
  /-- Other perfect (including from dedicated resultatives, or
      diachronic source undetermined). -/
  | other
  /-- No perfect category. -/
  | none
  deriving DecidableEq, Repr

/-- Whether a language has any perfect category. -/
def PerfectType.hasPerfect : PerfectType → Bool
  | .fromPossessive | .fromFinishAlready | .other => true
  | .none => false

-- ============================================================================
-- Types: WALS Chapter 69 — Position of Tense-Aspect Affixes
-- ============================================================================

/-- WALS Ch 69: Primary morphological strategy for tense-aspect marking.

    Languages with heterogeneous strategies where no single type is
    dominant are classified as `mixed`. Infixes and stem changes are
    treated as subtypes of prefixes/suffixes when localized at edges. -/
inductive TAAffixPosition where
  /-- Tense-aspect prefixes (primary strategy) -/
  | prefixing
  /-- Tense-aspect suffixes (primary strategy) -/
  | suffixing
  /-- Tense-aspect tone (primary strategy). Almost exclusively African. -/
  | tonal
  /-- Combination of strategies with none primary -/
  | mixed
  /-- No tense-aspect inflection -/
  | noInflection
  deriving DecidableEq, Repr

/-- Whether a language has any tense-aspect affixation. -/
def TAAffixPosition.hasAffixes : TAAffixPosition → Bool
  | .prefixing | .suffixing | .tonal | .mixed => true
  | .noInflection => false

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

/-- Convert WALS 65A enum to local `AspectMarking`. -/
private def fromWALS65A : Datasets.WALS.F65A.PerfectiveImperfective → AspectMarking
  | .grammaticalMarking => .grammatical
  | .noGrammaticalMarking => .none

/-- Convert WALS 66A enum to local `PastMarking`. -/
private def fromWALS66A : Datasets.WALS.F66A.PastTenseType → PastMarking
  | .presentNoRemotenessDistinctions => .marked
  | .present23RemotenessDistinctions => .markedRemoteness2_3
  | .present4OrMoreRemotenessDistinctions => .markedRemoteness4plus
  | .noPastTense => .none

/-- Convert WALS 67A enum to local `FutureMarking`. -/
private def fromWALS67A : Datasets.WALS.F67A.FutureTenseType → FutureMarking
  | .inflectionalFutureExists => .inflectional
  | .noInflectionalFuture => .none

/-- Convert WALS 68A enum to local `PerfectType`. -/
private def fromWALS68A : Datasets.WALS.F68A.PerfectType → PerfectType
  | .fromPossessive => .fromPossessive
  | .fromFinishAlready => .fromFinishAlready
  | .otherPerfect => .other
  | .noPerfect => .none

/-- Convert WALS 69A enum to local `TAAffixPosition`. -/
private def fromWALS69A : Datasets.WALS.F69A.TenseAspectAffixPosition → TAAffixPosition
  | .tenseAspectPrefixes => .prefixing
  | .tenseAspectSuffixes => .suffixing
  | .tenseAspectTone => .tonal
  | .mixedType => .mixed
  | .noTenseAspectInflection => .noInflection

-- ============================================================================
-- Language Profile Structure
-- ============================================================================

/-- A language's tense-aspect typological profile across WALS chapters 65-69. -/
structure TAProfile where
  /-- Language name -/
  language : String
  /-- ISO 639-3 code -/
  iso : String
  /-- Language family -/
  family : String
  /-- WALS Ch 65: perfective/imperfective aspect -/
  aspect : AspectMarking
  /-- WALS Ch 66: past tense marking -/
  past : PastMarking
  /-- WALS Ch 67: inflectional future -/
  future : FutureMarking
  /-- WALS Ch 68: perfect category -/
  perfect : PerfectType
  /-- WALS Ch 69: tense-aspect affix position -/
  affixPosition : TAAffixPosition
  deriving Repr, DecidableEq

-- ============================================================================
-- WALS Aggregate Distribution Data (derived from generated modules)
-- ============================================================================

/-- WALS Ch 65 distribution: perfective/imperfective aspect. -/
structure Ch65Counts where
  grammatical : Nat
  noMarking : Nat
  deriving Repr, DecidableEq

def ch65Dist : Ch65Counts :=
  { grammatical := (ch65.filter (·.value == .grammaticalMarking)).length
  , noMarking := (ch65.filter (·.value == .noGrammaticalMarking)).length }

/-- WALS Ch 66 distribution: past tense. -/
structure Ch66Counts where
  markedNoRemoteness : Nat
  markedRemoteness2_3 : Nat
  markedRemoteness4plus : Nat
  noMarking : Nat
  deriving Repr, DecidableEq

def ch66Dist : Ch66Counts :=
  { markedNoRemoteness := (ch66.filter (·.value == .presentNoRemotenessDistinctions)).length
  , markedRemoteness2_3 := (ch66.filter (·.value == .present23RemotenessDistinctions)).length
  , markedRemoteness4plus := (ch66.filter (·.value == .present4OrMoreRemotenessDistinctions)).length
  , noMarking := (ch66.filter (·.value == .noPastTense)).length }

/-- WALS Ch 67 distribution: inflectional future. -/
structure Ch67Counts where
  inflectional : Nat
  noInflectional : Nat
  deriving Repr, DecidableEq

def ch67Dist : Ch67Counts :=
  { inflectional := (ch67.filter (·.value == .inflectionalFutureExists)).length
  , noInflectional := (ch67.filter (·.value == .noInflectionalFuture)).length }

/-- WALS Ch 68 distribution: the perfect. -/
structure Ch68Counts where
  fromPossessive : Nat
  fromFinishAlready : Nat
  otherPerfect : Nat
  noPerfect : Nat
  deriving Repr, DecidableEq

def ch68Dist : Ch68Counts :=
  { fromPossessive := (ch68.filter (·.value == .fromPossessive)).length
  , fromFinishAlready := (ch68.filter (·.value == .fromFinishAlready)).length
  , otherPerfect := (ch68.filter (·.value == .otherPerfect)).length
  , noPerfect := (ch68.filter (·.value == .noPerfect)).length }

/-- WALS Ch 69 distribution: position of tense-aspect affixes. -/
structure Ch69Counts where
  prefixing : Nat
  suffixing : Nat
  tonal : Nat
  mixed : Nat
  noInflection : Nat
  deriving Repr, DecidableEq

def ch69Dist : Ch69Counts :=
  { prefixing := (ch69.filter (·.value == .tenseAspectPrefixes)).length
  , suffixing := (ch69.filter (·.value == .tenseAspectSuffixes)).length
  , tonal := (ch69.filter (·.value == .tenseAspectTone)).length
  , mixed := (ch69.filter (·.value == .mixedType)).length
  , noInflection := (ch69.filter (·.value == .noTenseAspectInflection)).length }

-- ============================================================================
-- Aggregate Data Verification (derived from WALS generated data)
-- ============================================================================

/-- Ch 65 sample size: 222 languages. -/
theorem ch65_total : ch65Dist.grammatical + ch65Dist.noMarking = 222 := by native_decide

/-- Ch 66 sample size: 222 languages. -/
theorem ch66_total : ch66Dist.markedNoRemoteness + ch66Dist.markedRemoteness2_3 +
          ch66Dist.markedRemoteness4plus + ch66Dist.noMarking = 222 := by native_decide

/-- Ch 67 sample size: 222 languages. -/
theorem ch67_total : ch67Dist.inflectional + ch67Dist.noInflectional = 222 := by native_decide

/-- Ch 68 sample size: 222 languages. -/
theorem ch68_total : ch68Dist.fromPossessive + ch68Dist.fromFinishAlready +
          ch68Dist.otherPerfect + ch68Dist.noPerfect = 222 := by native_decide

/-- Ch 69 sample size: 1131 languages. -/
theorem ch69_total : ch69Dist.prefixing + ch69Dist.suffixing + ch69Dist.tonal +
          ch69Dist.mixed + ch69Dist.noInflection = 1131 := by native_decide

-- ============================================================================
-- Language Data: Typologically Diverse Sample
-- ============================================================================

/--
English (Indo-European, Germanic).
Periphrastic perfective (simple past vs progressive), inflectional past,
no inflectional future (uses "will" — periphrastic), 'have'-perfect,
suffixing (-ed, -ing).
-/
def english : TAProfile :=
  { language := "English", iso := "eng", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .fromPossessive, affixPosition := .suffixing }

/--
Russian (Indo-European, Slavic).
Robust perfective/imperfective (typically via prefixation), inflectional past,
no inflectional future (periphrastic "budet" + infinitive for imperfective
future, perfective present = future), no perfect, suffixing (-l, -la for past).
-/
def russian : TAProfile :=
  { language := "Russian", iso := "rus", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .none, affixPosition := .suffixing }

/--
French (Indo-European, Romance).
Imparfait/passé composé aspect distinction, inflectional past
(passé simple), inflectional future (-ai, -as, -a...), 'have'-perfect
(avoir + past participle), suffixing.
-/
def french : TAProfile :=
  { language := "French", iso := "fra", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .fromPossessive, affixPosition := .suffixing }

/--
Spanish (Indo-European, Romance).
Imperfecto/preterito (imperfective/perfective), inflectional past and future,
'have'-perfect (haber + participle), suffixing.
-/
def spanish : TAProfile :=
  { language := "Spanish", iso := "spa", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .fromPossessive, affixPosition := .suffixing }

/--
Finnish (Uralic).
No grammatical perfective/imperfective, inflectional past (-i), no inflectional
future (present tense used for future reference), perfect (on + past participle,
'be'-type), suffixing.
-/
def finnish : TAProfile :=
  { language := "Finnish", iso := "fin", family := "Uralic"
  , aspect := .none, past := .marked, future := .none
  , perfect := .other, affixPosition := .suffixing }

/--
Turkish (Turkic).
Perfective/imperfective (-di vs -iyor), inflectional past, inflectional future
(-ecek), other perfect (-miş, from evidential/inferential), suffixing.
-/
def turkish : TAProfile :=
  { language := "Turkish", iso := "tur", family := "Turkic"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .other, affixPosition := .suffixing }

/--
Japanese (Japonic).
Perfective/imperfective (ta-form vs te-iru), inflectional past (-ta, -da),
no inflectional future, no distinct perfect, suffixing.
-/
def japanese : TAProfile :=
  { language := "Japanese", iso := "jpn", family := "Japonic"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .none, affixPosition := .suffixing }

/--
Korean (Koreanic).
Perfective/imperfective (-었- vs -고 있-), inflectional past (-었-),
inflectional future (-겠-), no distinct perfect, suffixing.
-/
def korean : TAProfile :=
  { language := "Korean", iso := "kor", family := "Koreanic"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .none, affixPosition := .suffixing }

/--
Mandarin Chinese (Sino-Tibetan).
Perfective le/guo, but these are particles (not inflectional), no inflectional
past, no inflectional future, no distinct perfect, no tense-aspect inflection.
Quintessential isolating language.
-/
def mandarin : TAProfile :=
  { language := "Mandarin Chinese", iso := "cmn", family := "Sino-Tibetan"
  , aspect := .grammatical, past := .none, future := .none
  , perfect := .none, affixPosition := .noInflection }

/--
Vietnamese (Austroasiatic).
No grammatical perfective/imperfective, no inflectional past, no inflectional
future, no perfect. Tense-aspect expressed by separate particles (da, se).
Part of the South-East Asian isolating area.
-/
def vietnamese : TAProfile :=
  { language := "Vietnamese", iso := "vie", family := "Austroasiatic"
  , aspect := .none, past := .none, future := .none
  , perfect := .none, affixPosition := .noInflection }

/--
Thai (Tai-Kadai).
No grammatical perfective/imperfective, no inflectional past, no inflectional
future, no perfect. South-East Asian isolating type.
-/
def thai : TAProfile :=
  { language := "Thai", iso := "tha", family := "Tai-Kadai"
  , aspect := .none, past := .none, future := .none
  , perfect := .none, affixPosition := .noInflection }

/--
Indonesian (Austronesian, Malayo-Polynesian).
No grammatical aspect, no past marking, no inflectional future, no perfect.
Classic example of tenselessness (air itu dingin = 'the water is/was cold').
Minor tense-aspect suffix exists (-i repetitive), but marginal.
-/
def indonesian : TAProfile :=
  { language := "Indonesian", iso := "ind", family := "Austronesian"
  , aspect := .none, past := .none, future := .none
  , perfect := .none, affixPosition := .suffixing }

/--
Swahili (Niger-Congo, Bantu).
Perfective/imperfective (-li-, -na-), past marking, no inflectional future,
other perfect (-me-), prefixing (T/A markers are verbal prefixes).
-/
def swahili : TAProfile :=
  { language := "Swahili", iso := "swh", family := "Niger-Congo"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .other, affixPosition := .prefixing }

/--
Yoruba (Niger-Congo, Atlantic-Congo).
Perfective/imperfective distinction, no past tense marking, no inflectional
future, perfect from 'already' (ti), no tense-aspect inflection (preverbal
particles).
-/
def yoruba : TAProfile :=
  { language := "Yoruba", iso := "yor", family := "Niger-Congo"
  , aspect := .grammatical, past := .none, future := .none
  , perfect := .fromFinishAlready, affixPosition := .noInflection }

/--
Hindi (Indo-European, Indo-Aryan).
Perfective/imperfective (-aa, -taa), inflectional past, inflectional future
(-egaa), other perfect, suffixing.
-/
def hindi : TAProfile :=
  { language := "Hindi", iso := "hin", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .other, affixPosition := .suffixing }

/--
Arabic (Egyptian) (Afro-Asiatic, Semitic).
Perfective/imperfective (katab/yiktib), inflectional past (perfective form
encodes past), no inflectional future (uses preverbal particles), no distinct
perfect, suffixing.
-/
def arabic : TAProfile :=
  { language := "Arabic (Egyptian)", iso := "arz", family := "Afro-Asiatic"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .none, affixPosition := .suffixing }

/--
Quechua (Quechuan).
No grammatical perfective/imperfective, inflectional past with 2-3 remoteness
distinctions (direct vs indirect past), inflectional future (-saq), other
perfect (-sqa resultative), suffixing.
-/
def quechua : TAProfile :=
  { language := "Quechua", iso := "que", family := "Quechuan"
  , aspect := .none, past := .markedRemoteness2_3, future := .inflectional
  , perfect := .other, affixPosition := .suffixing }

/--
Tagalog (Austronesian, Malayo-Polynesian).
Perfective/imperfective (completed vs contemplated aspect), no inflectional
past or future (aspect-based system), no distinct perfect, prefixing
(mag-, nag-, -um- etc.).
-/
def tagalog : TAProfile :=
  { language := "Tagalog", iso := "tgl", family := "Austronesian"
  , aspect := .grammatical, past := .none, future := .none
  , perfect := .none, affixPosition := .prefixing }

/--
Lango (Nilotic, Eastern Sudanic).
Perfective/imperfective/progressive marked primarily by tone, past tense
marking, no inflectional future, other perfect, tonal T/A marking.
-/
def lango : TAProfile :=
  { language := "Lango", iso := "laj", family := "Nilo-Saharan"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .other, affixPosition := .tonal }

/-- All languages in the sample. -/
def allLanguages : List TAProfile :=
  [ english, russian, french, spanish, finnish, turkish, japanese, korean
  , mandarin, vietnamese, thai, indonesian, swahili, yoruba, hindi, arabic
  , quechua, tagalog, lango ]

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

-- Verify representative language configurations
example : english.aspect = .grammatical := by native_decide
example : english.past = .marked := by native_decide
example : english.future = .none := by native_decide
example : english.perfect = .fromPossessive := by native_decide
example : english.affixPosition = .suffixing := by native_decide

example : mandarin.past = .none := by native_decide
example : mandarin.affixPosition = .noInflection := by native_decide

example : vietnamese.aspect = .none := by native_decide
example : vietnamese.past = .none := by native_decide
example : vietnamese.future = .none := by native_decide
example : vietnamese.affixPosition = .noInflection := by native_decide

example : swahili.affixPosition = .prefixing := by native_decide
example : lango.affixPosition = .tonal := by native_decide
example : quechua.past = .markedRemoteness2_3 := by native_decide

-- ============================================================================
-- WALS Grounding: Ch 65 (Perfective/Imperfective Aspect)
-- Languages where profile.aspect matches WALS 65A data.
-- Mismatches (eng, jpn, swa, yor): profile uses linguistically-informed
-- classifications that may disagree with WALS's operationalization.
-- ============================================================================

theorem russian_ch65 :
    (Datasets.WALS.F65A.lookup "rus").map (fromWALS65A ·.value) = some russian.aspect := by
  native_decide
theorem french_ch65 :
    (Datasets.WALS.F65A.lookup "fre").map (fromWALS65A ·.value) = some french.aspect := by
  native_decide
theorem spanish_ch65 :
    (Datasets.WALS.F65A.lookup "spa").map (fromWALS65A ·.value) = some spanish.aspect := by
  native_decide
theorem finnish_ch65 :
    (Datasets.WALS.F65A.lookup "fin").map (fromWALS65A ·.value) = some finnish.aspect := by
  native_decide
theorem turkish_ch65 :
    (Datasets.WALS.F65A.lookup "tur").map (fromWALS65A ·.value) = some turkish.aspect := by
  native_decide
theorem korean_ch65 :
    (Datasets.WALS.F65A.lookup "kor").map (fromWALS65A ·.value) = some korean.aspect := by
  native_decide
theorem mandarin_ch65 :
    (Datasets.WALS.F65A.lookup "mnd").map (fromWALS65A ·.value) = some mandarin.aspect := by
  native_decide
theorem vietnamese_ch65 :
    (Datasets.WALS.F65A.lookup "vie").map (fromWALS65A ·.value) = some vietnamese.aspect := by
  native_decide
theorem thai_ch65 :
    (Datasets.WALS.F65A.lookup "tha").map (fromWALS65A ·.value) = some thai.aspect := by
  native_decide
theorem indonesian_ch65 :
    (Datasets.WALS.F65A.lookup "ind").map (fromWALS65A ·.value) = some indonesian.aspect := by
  native_decide
theorem hindi_ch65 :
    (Datasets.WALS.F65A.lookup "hin").map (fromWALS65A ·.value) = some hindi.aspect := by
  native_decide
theorem arabic_ch65 :
    (Datasets.WALS.F65A.lookup "aeg").map (fromWALS65A ·.value) = some arabic.aspect := by
  native_decide
theorem tagalog_ch65 :
    (Datasets.WALS.F65A.lookup "tag").map (fromWALS65A ·.value) = some tagalog.aspect := by
  native_decide
theorem lango_ch65 :
    (Datasets.WALS.F65A.lookup "lan").map (fromWALS65A ·.value) = some lango.aspect := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 66 (The Past Tense)
-- Mismatch: Lango (WALS: noPastTense, profile: .marked).
-- ============================================================================

theorem english_ch66 :
    (Datasets.WALS.F66A.lookup "eng").map (fromWALS66A ·.value) = some english.past := by
  native_decide
theorem russian_ch66 :
    (Datasets.WALS.F66A.lookup "rus").map (fromWALS66A ·.value) = some russian.past := by
  native_decide
theorem french_ch66 :
    (Datasets.WALS.F66A.lookup "fre").map (fromWALS66A ·.value) = some french.past := by
  native_decide
theorem spanish_ch66 :
    (Datasets.WALS.F66A.lookup "spa").map (fromWALS66A ·.value) = some spanish.past := by
  native_decide
theorem finnish_ch66 :
    (Datasets.WALS.F66A.lookup "fin").map (fromWALS66A ·.value) = some finnish.past := by
  native_decide
theorem turkish_ch66 :
    (Datasets.WALS.F66A.lookup "tur").map (fromWALS66A ·.value) = some turkish.past := by
  native_decide
theorem japanese_ch66 :
    (Datasets.WALS.F66A.lookup "jpn").map (fromWALS66A ·.value) = some japanese.past := by
  native_decide
theorem korean_ch66 :
    (Datasets.WALS.F66A.lookup "kor").map (fromWALS66A ·.value) = some korean.past := by
  native_decide
theorem mandarin_ch66 :
    (Datasets.WALS.F66A.lookup "mnd").map (fromWALS66A ·.value) = some mandarin.past := by
  native_decide
theorem vietnamese_ch66 :
    (Datasets.WALS.F66A.lookup "vie").map (fromWALS66A ·.value) = some vietnamese.past := by
  native_decide
theorem thai_ch66 :
    (Datasets.WALS.F66A.lookup "tha").map (fromWALS66A ·.value) = some thai.past := by
  native_decide
theorem indonesian_ch66 :
    (Datasets.WALS.F66A.lookup "ind").map (fromWALS66A ·.value) = some indonesian.past := by
  native_decide
theorem swahili_ch66 :
    (Datasets.WALS.F66A.lookup "swa").map (fromWALS66A ·.value) = some swahili.past := by
  native_decide
theorem yoruba_ch66 :
    (Datasets.WALS.F66A.lookup "yor").map (fromWALS66A ·.value) = some yoruba.past := by
  native_decide
theorem hindi_ch66 :
    (Datasets.WALS.F66A.lookup "hin").map (fromWALS66A ·.value) = some hindi.past := by
  native_decide
theorem arabic_ch66 :
    (Datasets.WALS.F66A.lookup "aeg").map (fromWALS66A ·.value) = some arabic.past := by
  native_decide
theorem tagalog_ch66 :
    (Datasets.WALS.F66A.lookup "tag").map (fromWALS66A ·.value) = some tagalog.past := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 67 (The Future Tense)
-- Mismatches: Korean (WALS: noInflectionalFuture, profile: .inflectional),
--   Swahili (WALS: inflectionalFutureExists, profile: .none),
--   Arabic (WALS: inflectionalFutureExists, profile: .none),
--   Tagalog (WALS: inflectionalFutureExists, profile: .none).
-- ============================================================================

theorem english_ch67 :
    (Datasets.WALS.F67A.lookup "eng").map (fromWALS67A ·.value) = some english.future := by
  native_decide
theorem russian_ch67 :
    (Datasets.WALS.F67A.lookup "rus").map (fromWALS67A ·.value) = some russian.future := by
  native_decide
theorem french_ch67 :
    (Datasets.WALS.F67A.lookup "fre").map (fromWALS67A ·.value) = some french.future := by
  native_decide
theorem spanish_ch67 :
    (Datasets.WALS.F67A.lookup "spa").map (fromWALS67A ·.value) = some spanish.future := by
  native_decide
theorem finnish_ch67 :
    (Datasets.WALS.F67A.lookup "fin").map (fromWALS67A ·.value) = some finnish.future := by
  native_decide
theorem turkish_ch67 :
    (Datasets.WALS.F67A.lookup "tur").map (fromWALS67A ·.value) = some turkish.future := by
  native_decide
theorem japanese_ch67 :
    (Datasets.WALS.F67A.lookup "jpn").map (fromWALS67A ·.value) = some japanese.future := by
  native_decide
theorem mandarin_ch67 :
    (Datasets.WALS.F67A.lookup "mnd").map (fromWALS67A ·.value) = some mandarin.future := by
  native_decide
theorem vietnamese_ch67 :
    (Datasets.WALS.F67A.lookup "vie").map (fromWALS67A ·.value) = some vietnamese.future := by
  native_decide
theorem thai_ch67 :
    (Datasets.WALS.F67A.lookup "tha").map (fromWALS67A ·.value) = some thai.future := by
  native_decide
theorem indonesian_ch67 :
    (Datasets.WALS.F67A.lookup "ind").map (fromWALS67A ·.value) = some indonesian.future := by
  native_decide
theorem hindi_ch67 :
    (Datasets.WALS.F67A.lookup "hin").map (fromWALS67A ·.value) = some hindi.future := by
  native_decide
theorem yoruba_ch67 :
    (Datasets.WALS.F67A.lookup "yor").map (fromWALS67A ·.value) = some yoruba.future := by
  native_decide
theorem lango_ch67 :
    (Datasets.WALS.F67A.lookup "lan").map (fromWALS67A ·.value) = some lango.future := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 68 (The Perfect)
-- Mismatches: Turkish (WALS: noPerfect, profile: .other),
--   Vietnamese (WALS: otherPerfect, profile: .none),
--   Thai (WALS: fromFinishAlready, profile: .none),
--   Indonesian (WALS: fromFinishAlready, profile: .none),
--   Lango (WALS: noPerfect, profile: .other).
-- ============================================================================

theorem english_ch68 :
    (Datasets.WALS.F68A.lookup "eng").map (fromWALS68A ·.value) = some english.perfect := by
  native_decide
theorem russian_ch68 :
    (Datasets.WALS.F68A.lookup "rus").map (fromWALS68A ·.value) = some russian.perfect := by
  native_decide
theorem french_ch68 :
    (Datasets.WALS.F68A.lookup "fre").map (fromWALS68A ·.value) = some french.perfect := by
  native_decide
theorem spanish_ch68 :
    (Datasets.WALS.F68A.lookup "spa").map (fromWALS68A ·.value) = some spanish.perfect := by
  native_decide
theorem finnish_ch68 :
    (Datasets.WALS.F68A.lookup "fin").map (fromWALS68A ·.value) = some finnish.perfect := by
  native_decide
theorem japanese_ch68 :
    (Datasets.WALS.F68A.lookup "jpn").map (fromWALS68A ·.value) = some japanese.perfect := by
  native_decide
theorem korean_ch68 :
    (Datasets.WALS.F68A.lookup "kor").map (fromWALS68A ·.value) = some korean.perfect := by
  native_decide
theorem mandarin_ch68 :
    (Datasets.WALS.F68A.lookup "mnd").map (fromWALS68A ·.value) = some mandarin.perfect := by
  native_decide
theorem swahili_ch68 :
    (Datasets.WALS.F68A.lookup "swa").map (fromWALS68A ·.value) = some swahili.perfect := by
  native_decide
theorem yoruba_ch68 :
    (Datasets.WALS.F68A.lookup "yor").map (fromWALS68A ·.value) = some yoruba.perfect := by
  native_decide
theorem hindi_ch68 :
    (Datasets.WALS.F68A.lookup "hin").map (fromWALS68A ·.value) = some hindi.perfect := by
  native_decide
theorem arabic_ch68 :
    (Datasets.WALS.F68A.lookup "aeg").map (fromWALS68A ·.value) = some arabic.perfect := by
  native_decide
theorem tagalog_ch68 :
    (Datasets.WALS.F68A.lookup "tag").map (fromWALS68A ·.value) = some tagalog.perfect := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 69 (Position of Tense-Aspect Affixes)
-- Mismatches: Russian (WALS: mixedType, profile: .suffixing),
--   Mandarin (WALS: tenseAspectSuffixes, profile: .noInflection),
--   Arabic (WALS: mixedType, profile: .suffixing).
-- ============================================================================

theorem english_ch69 :
    (Datasets.WALS.F69A.lookup "eng").map (fromWALS69A ·.value) = some english.affixPosition := by
  native_decide
theorem french_ch69 :
    (Datasets.WALS.F69A.lookup "fre").map (fromWALS69A ·.value) = some french.affixPosition := by
  native_decide
theorem spanish_ch69 :
    (Datasets.WALS.F69A.lookup "spa").map (fromWALS69A ·.value) = some spanish.affixPosition := by
  native_decide
theorem finnish_ch69 :
    (Datasets.WALS.F69A.lookup "fin").map (fromWALS69A ·.value) = some finnish.affixPosition := by
  native_decide
theorem turkish_ch69 :
    (Datasets.WALS.F69A.lookup "tur").map (fromWALS69A ·.value) = some turkish.affixPosition := by
  native_decide
theorem japanese_ch69 :
    (Datasets.WALS.F69A.lookup "jpn").map (fromWALS69A ·.value) = some japanese.affixPosition := by
  native_decide
theorem korean_ch69 :
    (Datasets.WALS.F69A.lookup "kor").map (fromWALS69A ·.value) = some korean.affixPosition := by
  native_decide
theorem vietnamese_ch69 :
    (Datasets.WALS.F69A.lookup "vie").map (fromWALS69A ·.value) = some vietnamese.affixPosition := by
  native_decide
theorem thai_ch69 :
    (Datasets.WALS.F69A.lookup "tha").map (fromWALS69A ·.value) = some thai.affixPosition := by
  native_decide
theorem indonesian_ch69 :
    (Datasets.WALS.F69A.lookup "ind").map (fromWALS69A ·.value) = some indonesian.affixPosition := by
  native_decide
theorem swahili_ch69 :
    (Datasets.WALS.F69A.lookup "swa").map (fromWALS69A ·.value) = some swahili.affixPosition := by
  native_decide
theorem yoruba_ch69 :
    (Datasets.WALS.F69A.lookup "yor").map (fromWALS69A ·.value) = some yoruba.affixPosition := by
  native_decide
theorem hindi_ch69 :
    (Datasets.WALS.F69A.lookup "hin").map (fromWALS69A ·.value) = some hindi.affixPosition := by
  native_decide
theorem tagalog_ch69 :
    (Datasets.WALS.F69A.lookup "tag").map (fromWALS69A ·.value) = some tagalog.affixPosition := by
  native_decide
theorem lango_ch69 :
    (Datasets.WALS.F69A.lookup "lan").map (fromWALS69A ·.value) = some lango.affixPosition := by
  native_decide

-- ============================================================================
-- Generalization 1: Most languages have some past tense marking
-- ============================================================================

/-- Total languages with past marking in Ch 66. -/
def ch66TotalWithPast : Nat :=
  ch66Dist.markedNoRemoteness + ch66Dist.markedRemoteness2_3 + ch66Dist.markedRemoteness4plus

/-- A majority (134/222 = 60%) of WALS Ch 66 languages have past marking. -/
theorem past_marking_majority : ch66TotalWithPast > ch66Dist.noMarking := by
  native_decide

/-- Past marking total = 134 languages. -/
example : ch66TotalWithPast = 134 := by native_decide

-- ============================================================================
-- Generalization 2: Suffixing is overwhelmingly more common than prefixing
-- ============================================================================

/-- Suffixes outnumber prefixes by more than 4:1 (667 vs 153). -/
theorem suffix_dominant_over_prefix : ch69Dist.suffixing > 4 * ch69Dist.prefixing := by
  native_decide

/-- Suffixing is the most common T/A strategy overall. -/
theorem suffix_most_common :
    ch69Dist.suffixing > ch69Dist.prefixing ∧
    ch69Dist.suffixing > ch69Dist.tonal ∧
    ch69Dist.suffixing > ch69Dist.mixed ∧
    ch69Dist.suffixing > ch69Dist.noInflection := by
  native_decide

/-- Suffixes account for more than half of all languages in Ch 69. -/
theorem suffix_absolute_majority :
    ch69Dist.suffixing * 2 > ch69Dist.prefixing + ch69Dist.suffixing + ch69Dist.tonal +
                       ch69Dist.mixed + ch69Dist.noInflection := by
  native_decide

-- ============================================================================
-- Generalization 3: No evidence for tense-vs-aspect typological division
-- ============================================================================

/-- In the sample, languages with BOTH aspect and past marking outnumber
    languages with ONLY one of the two.

    @cite{dahl-velupillai-2013}: "there are considerably more languages in the
    sample that have both the aspectual and the temporal categories, or
    neither of the alternatives, than have one only." -/
def hasAspectAndPast (p : TAProfile) : Bool :=
  p.aspect == .grammatical && p.past.hasMarking

def hasAspectOnly (p : TAProfile) : Bool :=
  p.aspect == .grammatical && !p.past.hasMarking

def hasPastOnly (p : TAProfile) : Bool :=
  p.aspect != .grammatical && p.past.hasMarking

def hasNeitherAspectNorPast (p : TAProfile) : Bool :=
  p.aspect != .grammatical && !p.past.hasMarking

/-- In our sample: more languages have both aspect+past than aspect-only. -/
theorem both_exceeds_aspect_only :
    (allLanguages.filter hasAspectAndPast).length >
    (allLanguages.filter hasAspectOnly).length := by
  native_decide

/-- In our sample: more languages have both aspect+past than past-only. -/
theorem both_exceeds_past_only :
    (allLanguages.filter hasAspectAndPast).length >
    (allLanguages.filter hasPastOnly).length := by
  native_decide

-- ============================================================================
-- Generalization 4: South-East Asian isolating cluster
-- ============================================================================

/-- Whether a language lacks all three major T/A gram types from
    Chs 65-67 (no aspect, no past, no future). This is the hallmark of
    the South-East Asian isolating cluster. -/
def lacksMajorTAGrams (p : TAProfile) : Bool :=
  p.aspect == .none && p.past == .none && p.future == .none

/-- Vietnamese, Thai, and Indonesian all lack the three major T/A gram types:
    no grammaticalized perfective/imperfective, no past marking, no inflectional
    future.

    @cite{dahl-velupillai-2013}: "The languages in this area lack not only past
    tenses but also marking of the imperfective/perfective distinction and
    inflectional futures."

    Note: Indonesian has a minor repetitive suffix (-i) and so WALS classifies
    it as having T/A suffixes, but it lacks the major T/A categories. -/
theorem se_asian_isolating_cluster :
    lacksMajorTAGrams vietnamese = true ∧
    lacksMajorTAGrams thai = true ∧
    lacksMajorTAGrams indonesian = true := by
  native_decide

-- ============================================================================
-- Generalization 5: Future tense split is approximately even
-- ============================================================================

/-- Inflectional future is approximately 50/50 in Ch 67 (110 vs 112).
    Neither value constitutes a strong majority. -/
theorem future_near_even_split :
    ch67Dist.inflectional + ch67Dist.noInflectional = 222 ∧
    ch67Dist.inflectional > 100 ∧
    ch67Dist.noInflectional > 100 := by
  native_decide

-- ============================================================================
-- Generalization 6: 'Have'-perfects are geographically restricted
-- ============================================================================

/-- 'Have'-perfects (from possessive constructions) are extremely rare
    cross-linguistically — only 7 out of 222 languages. They are
    restricted almost exclusively to western Europe. -/
theorem have_perfect_rare : ch68Dist.fromPossessive < 10 := by
  native_decide

/-- Most languages lack a distinct perfect category entirely. -/
theorem no_perfect_majority : ch68Dist.noPerfect > ch68Dist.fromPossessive +
    ch68Dist.fromFinishAlready + ch68Dist.otherPerfect := by
  native_decide

-- ============================================================================
-- Generalization 7: Perfective/imperfective languages tend to have past
-- ============================================================================

/-- Among languages in our sample with grammatical perfective/imperfective
    aspect, the majority also have past tense marking.

    This supports Dahl & Velupillai's observation that aspect and tense
    tend to co-occur rather than being alternatives. -/
theorem aspect_languages_mostly_have_past :
    let withAspect := allLanguages.filter (·.aspect == .grammatical)
    let withAspectAndPast := withAspect.filter (·.past.hasMarking)
    withAspectAndPast.length > withAspect.length / 2 := by
  native_decide

-- ============================================================================
-- Generalization 8: Tone as T/A strategy is rare and mostly African
-- ============================================================================

/-- Tone as the primary tense-aspect strategy is extremely rare (13/1131). -/
theorem tone_ta_rare : ch69Dist.tonal < 15 := by
  native_decide

/-- In our sample, only Lango uses tone as the primary T/A strategy. -/
theorem tone_in_sample :
    (allLanguages.filter (·.affixPosition == .tonal)).length = 1 := by
  native_decide

-- ============================================================================
-- Generalization 9: Remoteness distinctions are uncommon
-- ============================================================================

/-- Most past-marking languages make no remoteness distinctions (94 out of
    134 with past marking). Languages with 4+ degrees of remoteness are
    extremely rare (only 2: Yagua being the richest with 5 degrees). -/
theorem remoteness_uncommon :
    ch66Dist.markedNoRemoteness > ch66Dist.markedRemoteness2_3 +
                               ch66Dist.markedRemoteness4plus := by
  native_decide

theorem extreme_remoteness_very_rare : ch66Dist.markedRemoteness4plus = 2 := by
  native_decide

-- ============================================================================
-- Generalization 10: 'Finish'/'already' perfects cluster geographically
-- ============================================================================

/-- Perfects from 'finish'/'already' are more common than 'have'-perfects
    (21 vs 7), concentrated in South-East Asia and West Africa. -/
theorem finish_perfect_more_common_than_have :
    ch68Dist.fromFinishAlready > ch68Dist.fromPossessive := by
  native_decide

/-- In our sample, Yoruba exemplifies the 'finish/already' perfect
    (ti = 'already'). -/
example : yoruba.perfect = .fromFinishAlready := by native_decide

-- ============================================================================
-- Cross-Chapter Interaction
-- ============================================================================

/-- Languages in our sample that lack ALL four T/A categories
    (no aspect, no past, no future, no perfect). -/
def lacksAllTA (p : TAProfile) : Bool :=
  p.aspect == .none && p.past == .none &&
  p.future == .none && p.perfect == .none

/-- There exist at least 2 languages in our sample with no T/A categories. -/
theorem ta_empty_nonempty :
    (allLanguages.filter lacksAllTA).length ≥ 2 := by
  native_decide

/-- Languages that lack all four T/A categories AND have no T/A inflection
    form the core of the South-East Asian isolating cluster.

    This matches the pattern described by @cite{dahl-velupillai-2013}:
    the same languages that lack tense and aspect grams are the
    isolating languages that lack inflectional morphology.

    Note: Indonesian has a minor repetitive suffix (-i) in WALS, so it
    has `lacksAllTA` but not `noInflection`. Vietnamese and Thai have both. -/
theorem ta_empty_and_no_inflection :
    let fullyIsolating := (allLanguages.filter lacksAllTA).filter
      (·.affixPosition == .noInflection)
    fullyIsolating.length ≥ 2 := by
  native_decide

-- ============================================================================
-- Types: WALS Chapter 78 — Coding of Evidentiality
-- ============================================================================

/-- WALS Ch 78: How evidentiality is coded in the language.

    "Evidentiality" here means grammaticalized marking of information source.
    Languages differ in whether evidentiality is part of the tense system,
    expressed by verbal affixes, clitics, particles, or not grammaticalized. -/
inductive EvidentialityCoding where
  /-- No grammatical evidentiality -/
  | none
  /-- Evidentiality is part of the tense paradigm (e.g., Turkish -miş) -/
  | partOfTense
  /-- Evidentiality marked by verbal affix -/
  | verbalAffix
  /-- Evidentiality marked by clitic -/
  | clitic
  /-- Evidentiality marked by particle -/
  | particle
  /-- Other strategy -/
  | other
  deriving DecidableEq, Repr

/-- Whether a language has any grammatical evidentiality. -/
def EvidentialityCoding.hasEvidentiality : EvidentialityCoding → Bool
  | .none => false
  | _ => true

-- ============================================================================
-- TAMEProfile: Unified Tense-Aspect-Mood-Evidentiality Profile
-- ============================================================================

/-- A language's typological profile across the full TAME space:
    tense (Ch 66–67), aspect (Ch 65), perfect (Ch 68), morphological
    position (Ch 69), and evidentiality (Ch 78).

    Extends `TAProfile` with the evidentiality dimension. -/
structure TAMEProfile where
  /-- Language name -/
  language : String
  /-- ISO 639-3 code -/
  iso : String
  /-- Language family -/
  family : String
  /-- WALS Ch 65: perfective/imperfective aspect -/
  aspect : AspectMarking
  /-- WALS Ch 66: past tense marking -/
  past : PastMarking
  /-- WALS Ch 67: inflectional future -/
  future : FutureMarking
  /-- WALS Ch 68: perfect category -/
  perfect : PerfectType
  /-- WALS Ch 69: tense-aspect affix position -/
  affixPosition : TAAffixPosition
  /-- WALS Ch 78: coding of evidentiality -/
  evidentiality : EvidentialityCoding
  deriving Repr, DecidableEq

-- ============================================================================
-- Sample Language TAMEProfiles
-- ============================================================================

/--
Turkish (Turkic). Evidentiality is part of the tense paradigm:
-miş marks indirect evidence (hearsay/inference) vs -di (direct).
-/
def turkishTAME : TAMEProfile :=
  { language := "Turkish", iso := "tur", family := "Turkic"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .other, affixPosition := .suffixing
  , evidentiality := .partOfTense }

/--
Quechua (Quechuan). Evidentiality via verbal suffixes:
-mi (direct), -si (hearsay), -chá (conjecture).
-/
def quechuaTAME : TAMEProfile :=
  { language := "Quechua", iso := "que", family := "Quechuan"
  , aspect := .none, past := .markedRemoteness2_3, future := .inflectional
  , perfect := .other, affixPosition := .suffixing
  , evidentiality := .verbalAffix }

/--
Korean (Koreanic). Evidentiality via verbal suffixes:
-te (retrospective evidential), -ney (contemporaneous evidential).
@cite{cumming-2026} analyzes these as tense-evidential interactions.
-/
def koreanTAME : TAMEProfile :=
  { language := "Korean", iso := "kor", family := "Koreanic"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .none, affixPosition := .suffixing
  , evidentiality := .verbalAffix }

/--
English (Indo-European). No grammatical evidentiality.
Evidential distinctions are expressed lexically ("apparently",
"I heard that..."), not grammatically.
-/
def englishTAME : TAMEProfile :=
  { language := "English", iso := "eng", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .fromPossessive, affixPosition := .suffixing
  , evidentiality := .none }

/--
Mandarin Chinese (Sino-Tibetan). No grammatical evidentiality,
no tense-aspect inflection. Isolating type.
-/
def mandarinTAME : TAMEProfile :=
  { language := "Mandarin Chinese", iso := "cmn", family := "Sino-Tibetan"
  , aspect := .grammatical, past := .none, future := .none
  , perfect := .none, affixPosition := .noInflection
  , evidentiality := .none }

/-- All TAME-profiled languages. -/
def allTAMELanguages : List TAMEProfile :=
  [turkishTAME, quechuaTAME, koreanTAME, englishTAME, mandarinTAME]

-- ============================================================================
-- Generalization 11: Evidentiality co-occurs with tense/aspect marking
-- ============================================================================

/-- Whether a `TAMEProfile` has any tense or aspect marking
    (aspect, past, or future). -/
def TAMEProfile.hasTenseOrAspect (p : TAMEProfile) : Bool :=
  p.aspect == .grammatical || p.past.hasMarking || p.future == .inflectional

/-- In our TAME sample, every language with grammatical evidentiality
    also has tense or aspect marking.

    This reinforces the "no tense-vs-aspect divide" finding (Generalization 3)
    by showing that evidentiality also clusters with tense/aspect marking
    rather than replacing it. -/
theorem evidential_implies_tense_aspect :
    (allTAMELanguages.filter (·.evidentiality.hasEvidentiality)).all
      (·.hasTenseOrAspect) = true := by
  native_decide

-- ============================================================================
-- Per-Language TAME Verification
-- ============================================================================

example : turkishTAME.evidentiality = .partOfTense := by native_decide
example : quechuaTAME.evidentiality = .verbalAffix := by native_decide
example : koreanTAME.evidentiality = .verbalAffix := by native_decide
example : englishTAME.evidentiality = .none := by native_decide
example : mandarinTAME.evidentiality = .none := by native_decide

end Phenomena.TenseAspect.Typology
