import Linglib.Core.Basic

/-!
# Cross-Linguistic Typology of Tense and Aspect (WALS Chapters 65--69)

Cross-linguistic data on tense-aspect systems from the World Atlas of Language
Structures (WALS), covering five parameters:

- **Ch 65 (Perfective/Imperfective Aspect)**: Whether a language grammaticalizes
  the perfective/imperfective distinction. 222 languages, two values.
  (Dahl & Velupillai 2013a)

- **Ch 66 (The Past Tense)**: Whether a language has grammatical marking of
  past tense, and if so how many remoteness distinctions it makes. 222 languages,
  four values. (Dahl & Velupillai 2013b)

- **Ch 67 (The Future Tense)**: Whether a language has inflectional marking of
  future tense. 222 languages, two values. (Dahl & Velupillai 2013c)

- **Ch 68 (The Perfect)**: Whether a language has a distinct perfect category
  (resultative + experiential uses), and its diachronic source. 222 languages,
  four values. (Dahl & Velupillai 2013d)

- **Ch 69 (Position of Tense-Aspect Affixes)**: How tense-aspect is
  morphologically expressed. 1062 languages, five values. (Dryer 2013)

## Key findings

Dahl & Velupillai (2013) note that there is no evidence for a typological
division into "tense languages" vs "aspect languages" -- languages that have
aspectual marking tend also to have tense marking. Suffixing is overwhelmingly
the dominant strategy for tense-aspect morphology (Dryer 2013). South-East
Asian languages consistently lack morphological tense-aspect marking.

## References

- Dahl, O. & Velupillai, V. (2013a). Perfective/Imperfective Aspect. In
  Dryer & Haspelmath (eds.), WALS Online. https://wals.info/chapter/65
- Dahl, O. & Velupillai, V. (2013b). The Past Tense. In Dryer & Haspelmath
  (eds.), WALS Online. https://wals.info/chapter/66
- Dahl, O. & Velupillai, V. (2013c). The Future Tense. In Dryer & Haspelmath
  (eds.), WALS Online. https://wals.info/chapter/67
- Dahl, O. & Velupillai, V. (2013d). The Perfect. In Dryer & Haspelmath
  (eds.), WALS Online. https://wals.info/chapter/68
- Dryer, M. (2013). Position of Tense-Aspect Affixes. In Dryer & Haspelmath
  (eds.), WALS Online. https://wals.info/chapter/69
- Comrie, B. (1985). Tense. Cambridge University Press.
- Bybee, J., Perkins, R. & Pagliuca, W. (1994). The Evolution of Grammar.
  University of Chicago Press.
-/

namespace Phenomena.TenseAspect.Typology

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

/-- Whether a language has any tense-aspect affixation. -/
def TAAffixPosition.hasAffixes : TAAffixPosition → Bool
  | .prefixing | .suffixing | .tonal | .mixed => true
  | .noInflection => false

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
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- WALS Aggregate Distribution Data
-- ============================================================================

/-- WALS Ch 65 distribution: perfective/imperfective aspect (222 languages). -/
structure Ch65Counts where
  grammatical : Nat    -- 101
  noMarking : Nat      -- 121
  deriving Repr, DecidableEq, BEq

def ch65 : Ch65Counts := { grammatical := 101, noMarking := 121 }

/-- WALS Ch 66 distribution: past tense (222 languages). -/
structure Ch66Counts where
  markedNoRemoteness : Nat     -- 94
  markedRemoteness2_3 : Nat    -- 38
  markedRemoteness4plus : Nat  -- 2
  noMarking : Nat              -- 88
  deriving Repr, DecidableEq, BEq

def ch66 : Ch66Counts :=
  { markedNoRemoteness := 94, markedRemoteness2_3 := 38
  , markedRemoteness4plus := 2, noMarking := 88 }

/-- WALS Ch 67 distribution: inflectional future (222 languages). -/
structure Ch67Counts where
  inflectional : Nat   -- 110
  noInflectional : Nat -- 112
  deriving Repr, DecidableEq, BEq

def ch67 : Ch67Counts := { inflectional := 110, noInflectional := 112 }

/-- WALS Ch 68 distribution: the perfect (222 languages). -/
structure Ch68Counts where
  fromPossessive : Nat      -- 7
  fromFinishAlready : Nat   -- 21
  otherPerfect : Nat        -- 80
  noPerfect : Nat           -- 114
  deriving Repr, DecidableEq, BEq

def ch68 : Ch68Counts :=
  { fromPossessive := 7, fromFinishAlready := 21
  , otherPerfect := 80, noPerfect := 114 }

/-- WALS Ch 69 distribution: position of tense-aspect affixes (1062 languages). -/
structure Ch69Counts where
  prefixing : Nat    -- 150
  suffixing : Nat    -- 629
  tonal : Nat        -- 11
  mixed : Nat        -- 133
  noInflection : Nat -- 139
  deriving Repr, DecidableEq, BEq

def ch69 : Ch69Counts :=
  { prefixing := 150, suffixing := 629, tonal := 11, mixed := 133, noInflection := 139 }

-- ============================================================================
-- Aggregate Data Verification
-- ============================================================================

/-- Ch 65 sample size: 222 languages. -/
example : ch65.grammatical + ch65.noMarking = 222 := by native_decide

/-- Ch 66 sample size: 222 languages. -/
example : ch66.markedNoRemoteness + ch66.markedRemoteness2_3 +
          ch66.markedRemoteness4plus + ch66.noMarking = 222 := by native_decide

/-- Ch 67 sample size: 222 languages. -/
example : ch67.inflectional + ch67.noInflectional = 222 := by native_decide

/-- Ch 68 sample size: 222 languages. -/
example : ch68.fromPossessive + ch68.fromFinishAlready +
          ch68.otherPerfect + ch68.noPerfect = 222 := by native_decide

/-- Ch 69 sample size: 1062 languages. -/
example : ch69.prefixing + ch69.suffixing + ch69.tonal +
          ch69.mixed + ch69.noInflection = 1062 := by native_decide

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
-- Generalization 1: Most languages have some past tense marking
-- ============================================================================

/-- Total languages with past marking in Ch 66. -/
def ch66TotalWithPast : Nat :=
  ch66.markedNoRemoteness + ch66.markedRemoteness2_3 + ch66.markedRemoteness4plus

/-- A majority (134/222 = 60%) of WALS Ch 66 languages have past marking. -/
theorem past_marking_majority : ch66TotalWithPast > ch66.noMarking := by
  native_decide

/-- Past marking total = 134 languages. -/
example : ch66TotalWithPast = 134 := by native_decide

-- ============================================================================
-- Generalization 2: Suffixing is overwhelmingly more common than prefixing
-- ============================================================================

/-- Suffixes outnumber prefixes by more than 4:1 (629 vs 150). -/
theorem suffix_dominant_over_prefix : ch69.suffixing > 4 * ch69.prefixing := by
  native_decide

/-- Suffixing is the most common T/A strategy overall. -/
theorem suffix_most_common :
    ch69.suffixing > ch69.prefixing ∧
    ch69.suffixing > ch69.tonal ∧
    ch69.suffixing > ch69.mixed ∧
    ch69.suffixing > ch69.noInflection := by
  native_decide

/-- Suffixes account for more than half of all languages in Ch 69. -/
theorem suffix_absolute_majority :
    ch69.suffixing * 2 > ch69.prefixing + ch69.suffixing + ch69.tonal +
                       ch69.mixed + ch69.noInflection := by
  native_decide

-- ============================================================================
-- Generalization 3: No evidence for tense-vs-aspect typological division
-- ============================================================================

/-- In the sample, languages with BOTH aspect and past marking outnumber
    languages with ONLY one of the two.

    Dahl & Velupillai (2013): "there are considerably more languages in the
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

    Dahl & Velupillai (2013): "The languages in this area lack not only past
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
    ch67.inflectional + ch67.noInflectional = 222 ∧
    ch67.inflectional > 100 ∧
    ch67.noInflectional > 100 := by
  native_decide

-- ============================================================================
-- Generalization 6: 'Have'-perfects are geographically restricted
-- ============================================================================

/-- 'Have'-perfects (from possessive constructions) are extremely rare
    cross-linguistically — only 7 out of 222 languages. They are
    restricted almost exclusively to western Europe. -/
theorem have_perfect_rare : ch68.fromPossessive < 10 := by
  native_decide

/-- Most languages lack a distinct perfect category entirely. -/
theorem no_perfect_majority : ch68.noPerfect > ch68.fromPossessive +
    ch68.fromFinishAlready + ch68.otherPerfect := by
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

/-- Tone as the primary tense-aspect strategy is extremely rare (11/1062). -/
theorem tone_ta_rare : ch69.tonal < 15 := by
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
    ch66.markedNoRemoteness > ch66.markedRemoteness2_3 +
                               ch66.markedRemoteness4plus := by
  native_decide

theorem extreme_remoteness_very_rare : ch66.markedRemoteness4plus = 2 := by
  native_decide

-- ============================================================================
-- Generalization 10: 'Finish'/'already' perfects cluster geographically
-- ============================================================================

/-- Perfects from 'finish'/'already' are more common than 'have'-perfects
    (21 vs 7), concentrated in South-East Asia and West Africa. -/
theorem finish_perfect_more_common_than_have :
    ch68.fromFinishAlready > ch68.fromPossessive := by
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

    This matches the pattern described by Dahl & Velupillai (2013):
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

/-- WALS Ch 78: How evidentiality is coded in the language (de Haan 2013).

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
  deriving DecidableEq, BEq, Repr

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
  deriving Repr, DecidableEq, BEq

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
Cumming (2026) analyzes these as tense-evidential interactions.
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
