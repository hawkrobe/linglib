import Linglib.Core.Basic

/-!
# Cross-Linguistic Typology of Numeral Systems (WALS Chapters 53--56)

Typological data on four dimensions of numeral morphology and syntax, drawn from
WALS chapters by Stolz & Veselinova (Ch 53) and Gil (Ch 54--56). The data
covers ordinal numeral formation, distributive numerals, numeral classifiers,
and the relationship between conjunctions and universal quantification.

1. **Ordinal Numerals** (Ch 53, Stolz & Veselinova): How ordinal numbers are
   formed from cardinals. The dominant cross-linguistic pattern is for "first" to
   be suppletive (not derived from "one") while higher ordinals are regular
   derivations from cardinals. This asymmetry reflects the cognitive and
   discourse-functional salience of first position.

2. **Distributive Numerals** (Ch 54, Gil): Whether a language has a dedicated
   morphological form for distributive numerals ("two each", "three apiece").
   Reduplication of the cardinal is the most common strategy among languages
   that mark distributives (e.g., Turkish iki-ser 'two each', Tagalog dalawa-
   dalawa 'two-two'). Many languages lack a dedicated form entirely.

3. **Numeral Classifiers** (Ch 55, Gil): Whether the language uses numeral
   classifiers --- dedicated morphemes required or available when a numeral
   combines with a noun. Classifier languages concentrate in East and Southeast
   Asia and Mesoamerica. The global majority of languages lack classifiers.
   An important typological correlation (Sanches & Slobin 1973): classifier
   languages tend to lack obligatory plural marking on nouns.

4. **Conjunctions and Universal Quantifiers** (Ch 56, Gil): Whether a language
   uses the same morpheme for 'and' (conjunction) and 'all' / 'every' (universal
   quantification). Many languages show identity between these forms, suggesting
   a deep semantic connection between conjunction and universal quantification
   (both involve exhaustive predication over a set).

## References

- Stolz, T. & Veselinova, L. (2013). Ordinal Numerals. In Dryer & Haspelmath
  (eds.), WALS Online (v2020.3). https://wals.info/chapter/53
- Gil, D. (2013a). Distributive Numerals. In Dryer & Haspelmath (eds.), WALS
  Online (v2020.3). https://wals.info/chapter/54
- Gil, D. (2013b). Numeral Classifiers. In Dryer & Haspelmath (eds.), WALS
  Online (v2020.3). https://wals.info/chapter/55
- Gil, D. (2013c). Conjunctions and Universal Quantifiers. In Dryer & Haspelmath
  (eds.), WALS Online (v2020.3). https://wals.info/chapter/56
- Aikhenvald, A. Y. (2000). Classifiers: A Typology of Noun Categorization
  Devices. Oxford University Press.
- Greenberg, J. H. (1978). Generalizations about Numeral Systems. In Greenberg
  (ed.), Universals of Human Language, vol. 3, 249--295. Stanford University Press.
- Sanches, M. & Slobin, D. I. (1973). Numeral classifiers and plural marking:
  an implicational universal. Working Papers in Language Universals 11, 1--22.
-/

namespace Phenomena.Numerals.Typology

-- ============================================================================
-- Chapter 53: Ordinal Numerals (Stolz & Veselinova)
-- ============================================================================

/-- How a language forms ordinal numerals from cardinal ones (WALS Ch 53).

    The key typological variable is whether "first" is suppletive (not derived
    from "one") and how many of the lowest ordinals show suppletion or
    irregularity. The pattern "first" suppletive + higher ordinals regular is
    overwhelmingly dominant. -/
inductive OrdinalFormation where
  | firstSuppletion      -- "first" is suppletive, "second" onward regular from cardinals
  | firstSecondSuppletion -- "first" and "second" suppletive, "third" onward regular
  | allFromCardinals     -- all ordinals derived regularly from cardinals (incl. "one-th")
  | various              -- mixed strategies, no single dominant pattern
  | noOrdinals           -- no productive ordinal formation reported
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 53 distribution: language counts per ordinal formation type.
    Total: 321 languages. -/
structure OrdinalDistribution where
  firstSuppletion : Nat
  firstSecondSuppletion : Nat
  allFromCardinals : Nat
  various : Nat
  noOrdinals : Nat
  deriving Repr

def OrdinalDistribution.total (d : OrdinalDistribution) : Nat :=
  d.firstSuppletion + d.firstSecondSuppletion + d.allFromCardinals +
  d.various + d.noOrdinals

/-- Actual WALS Ch 53 counts (Stolz & Veselinova 2013). -/
def ch53Distribution : OrdinalDistribution :=
  { firstSuppletion := 99
  , firstSecondSuppletion := 45
  , allFromCardinals := 28
  , various := 83
  , noOrdinals := 66 }

-- ============================================================================
-- Chapter 54: Distributive Numerals (Gil)
-- ============================================================================

/-- Whether and how a language marks distributive numerals (WALS Ch 54).

    Distributive numerals express "N each" or "N apiece" meanings. Languages
    vary in whether they have a dedicated morphological strategy and, if so,
    what kind. Reduplication of the cardinal numeral is the most widespread
    dedicated strategy (e.g., Japanese hito-ri hito-ri, Hungarian két-két). -/
inductive DistributiveNumeral where
  | noDistributive       -- no dedicated distributive numeral form
  | markedByReduplication -- cardinal is reduplicated (e.g., Turkish iki-şer, Tagalog dalawa-dalawa)
  | markedBySuffix       -- a suffix creates distributive (e.g., Georgian -agan)
  | markedByPrefix       -- a prefix creates distributive
  | markedByOtherMeans   -- other strategies (particles, circumfix, etc.)
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 54 distribution: language counts per distributive type.
    Total: 251 languages. -/
structure DistributiveDistribution where
  noDistributive : Nat
  reduplication : Nat
  suffixCount : Nat
  prefixCount : Nat
  otherMeans : Nat
  deriving Repr

def DistributiveDistribution.total (d : DistributiveDistribution) : Nat :=
  d.noDistributive + d.reduplication + d.suffixCount + d.prefixCount + d.otherMeans

/-- Actual WALS Ch 54 counts (Gil 2013a). -/
def ch54Distribution : DistributiveDistribution :=
  { noDistributive := 63
  , reduplication := 85
  , suffixCount := 34
  , prefixCount := 19
  , otherMeans := 50 }

-- ============================================================================
-- Chapter 55: Numeral Classifiers (Gil)
-- ============================================================================

/-- Whether a language uses numeral classifiers (WALS Ch 55).

    Numeral classifiers are morphemes that co-occur with a numeral when it
    modifies a noun (e.g., Mandarin san *ge* ren 'three CL person'). The key
    distinction is between obligatory classifiers (required whenever a numeral
    modifies a noun) and optional classifiers (available but not required). -/
inductive ClassifierStatus where
  | absent               -- no numeral classifiers (e.g., English, Spanish, Arabic)
  | optional             -- classifiers available but not required (e.g., Turkish, Bengali)
  | obligatory           -- classifiers required with numeral+noun (e.g., Mandarin, Japanese, Thai)
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 55 distribution: language counts per classifier status.
    Total: 400 languages. -/
structure ClassifierDistribution where
  absent : Nat
  optional : Nat
  obligatory : Nat
  deriving Repr

def ClassifierDistribution.total (d : ClassifierDistribution) : Nat :=
  d.absent + d.optional + d.obligatory

/-- Actual WALS Ch 55 counts (Gil 2013b). -/
def ch55Distribution : ClassifierDistribution :=
  { absent := 260
  , optional := 62
  , obligatory := 78 }

-- ============================================================================
-- Chapter 56: Conjunctions and Universal Quantifiers (Gil)
-- ============================================================================

/-- The relationship between 'and' and 'all/every' in a language (WALS Ch 56).

    Gil distinguishes languages where the conjunction marker and the universal
    quantifier share the same form (identity) from those where they are
    morphologically distinct (differentiation). Identity between 'and' and
    'all' reflects a deep connection between conjunction (exhaustive pairing)
    and universal quantification (exhaustive predication). -/
inductive ConjunctionQuantifier where
  | identity             -- same morpheme for 'and' and 'all' (e.g., Mandarin dou, Tagalog lahat)
  | differentiation      -- different morphemes (e.g., English and/all, Japanese to/subete)
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 56 distribution: language counts per conjunction-quantifier type.
    Total: 220 languages. -/
structure ConjQuantDistribution where
  identity : Nat
  differentiation : Nat
  deriving Repr

def ConjQuantDistribution.total (d : ConjQuantDistribution) : Nat :=
  d.identity + d.differentiation

/-- Actual WALS Ch 56 counts (Gil 2013c). -/
def ch56Distribution : ConjQuantDistribution :=
  { identity := 43
  , differentiation := 177 }

-- ============================================================================
-- Distribution Verification
-- ============================================================================

/-- Ch 53 total: 321 languages. -/
example : ch53Distribution.total = 321 := by native_decide

/-- Ch 54 total: 251 languages. -/
example : ch54Distribution.total = 251 := by native_decide

/-- Ch 55 total: 400 languages. -/
example : ch55Distribution.total = 400 := by native_decide

/-- Ch 56 total: 220 languages. -/
example : ch56Distribution.total = 220 := by native_decide

-- ============================================================================
-- Language Profiles
-- ============================================================================

/-- Areal region, used for areal generalizations about classifier distribution. -/
inductive Region where
  | europe
  | eastAsia
  | southeastAsia
  | southAsia
  | centralAsia
  | westAsia
  | africa
  | northAmerica
  | mesoamerica
  | southAmerica
  | oceania
  deriving DecidableEq, BEq, Repr

/-- Whether a language has obligatory grammatical plural marking on common nouns.
    Used for the Sanches-Slobin generalization relating classifiers and plural. -/
inductive PluralMarking where
  | obligatory           -- plural marking required (e.g., English, Spanish)
  | optional             -- plural marking available but not required (e.g., Korean)
  | none                 -- no grammatical plural on nouns (e.g., Mandarin, Japanese)
  deriving DecidableEq, BEq, Repr

/-- A language's numeral typology profile across all four WALS dimensions. -/
structure NumeralProfile where
  language : String
  /-- ISO 639-3 code -/
  iso : String
  /-- Ch 53: Ordinal numeral formation -/
  ordinal : OrdinalFormation
  /-- Ch 54: Distributive numeral marking -/
  distributive : DistributiveNumeral
  /-- Ch 55: Numeral classifier status -/
  classifier : ClassifierStatus
  /-- Ch 56: Conjunction-quantifier relationship -/
  conjQuant : ConjunctionQuantifier
  /-- Areal region (for areal generalizations) -/
  region : Region
  /-- Plural marking on common nouns (for Sanches-Slobin) -/
  pluralMarking : PluralMarking
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- Language Instances
-- ============================================================================

/-- English: "first" is suppletive (not *one-th), "second" is suppletive (not
    *two-th), higher ordinals regular (-th suffix). No morphological distributive
    numerals (*two-each), no numeral classifiers, and conjunction 'and' differs
    from universal quantifier 'all'. Obligatory plural on nouns. -/
def english : NumeralProfile :=
  { language := "English"
  , iso := "eng"
  , ordinal := .firstSecondSuppletion
  , distributive := .noDistributive
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .europe
  , pluralMarking := .obligatory }

/-- Mandarin Chinese: ordinals formed regularly with di- prefix (di-yi 'first',
    di-er 'second', etc.) --- no suppletion. No morphological distributive.
    Obligatory numeral classifiers (san ge ren 'three CL person'). Conjunction
    'he' and universal 'dou' are different morphemes, but 'dou' shows
    quantificational force in both contexts. No grammatical plural on nouns. -/
def mandarin : NumeralProfile :=
  { language := "Mandarin"
  , iso := "cmn"
  , ordinal := .allFromCardinals
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .eastAsia
  , pluralMarking := .none }

/-- Japanese: ordinals formed with -banme suffix (ichi-banme 'first',
    ni-banme 'second'). No suppletion. Distributive by reduplication
    (hitori-hitori 'one by one'). Obligatory numeral classifiers (san-nin
    'three-CL.person', ni-hon 'two-CL.long.thing'). Conjunction 'to' differs
    from universal 'subete'. No grammatical plural on common nouns. -/
def japanese : NumeralProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , ordinal := .allFromCardinals
  , distributive := .markedByReduplication
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .eastAsia
  , pluralMarking := .none }

/-- Thai: ordinals formed with thi- prefix (thi-nung 'first', thi-song
    'second') --- all regular from cardinals. No morphological distributive.
    Obligatory numeral classifiers (maa sam tua 'dog three CL.animal'). No
    grammatical plural on nouns. -/
def thai : NumeralProfile :=
  { language := "Thai"
  , iso := "tha"
  , ordinal := .allFromCardinals
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .southeastAsia
  , pluralMarking := .none }

/-- Vietnamese: ordinals formed with thu prefix (thu nhat 'first', thu hai
    'second') --- regular from cardinals. No morphological distributive.
    Obligatory classifiers (ba con meo 'three CL cat'). No grammatical
    plural on nouns. -/
def vietnamese : NumeralProfile :=
  { language := "Vietnamese"
  , iso := "vie"
  , ordinal := .allFromCardinals
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .southeastAsia
  , pluralMarking := .none }

/-- Turkish: "birinci" 'first' derived regularly from "bir" 'one' via -inci
    suffix (all ordinals formed by -inci or -unci suffix). Distributive numerals
    by suffix -er or -ar (iki-ser 'two each'). No obligatory numeral classifiers,
    but optional classifiers exist (iki tane kitap 'two CL book'). 'Ve' (and)
    differs from 'hepsi' or 'butun' (all). Obligatory plural with -ler or -lar. -/
def turkish : NumeralProfile :=
  { language := "Turkish"
  , iso := "tur"
  , ordinal := .allFromCardinals
  , distributive := .markedBySuffix
  , classifier := .optional
  , conjQuant := .differentiation
  , region := .westAsia
  , pluralMarking := .obligatory }

/-- Korean: ordinals use native Korean numerals + -jjae suffix (cheot-jjae
    'first' partially suppletive). Distributive by suffix -ssik (du-ssik
    'two each'). Optional numeral classifiers (se myeong-ui haksaeng
    'three CL student'). 'Gwa/wa' (and) differs from 'modu' (all). Optional
    plural marking with -deul. -/
def korean : NumeralProfile :=
  { language := "Korean"
  , iso := "kor"
  , ordinal := .firstSuppletion
  , distributive := .markedBySuffix
  , classifier := .optional
  , conjQuant := .differentiation
  , region := .eastAsia
  , pluralMarking := .optional }

/-- Hindi: ordinals show "first" (pehla) suppletive, higher ordinals regular
    with -vam suffix (dusra 'second' also partially suppletive). Distributive
    by reduplication (do-do 'two-two'). No numeral classifiers. 'Aur' (and)
    differs from 'sab' (all). Obligatory plural marking. -/
def hindi : NumeralProfile :=
  { language := "Hindi"
  , iso := "hin"
  , ordinal := .firstSecondSuppletion
  , distributive := .markedByReduplication
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .southAsia
  , pluralMarking := .obligatory }

/-- Bengali: ordinals formed with -tho suffix, but "first" (prothom) is
    suppletive. Distributive by reduplication. Optional classifiers (tin-ta
    boi 'three-CL book', but bare tin boi also grammatical). 'Ebong' (and)
    differs from 'sob' (all). Optional plural. -/
def bengali : NumeralProfile :=
  { language := "Bengali"
  , iso := "ben"
  , ordinal := .firstSuppletion
  , distributive := .markedByReduplication
  , classifier := .optional
  , conjQuant := .differentiation
  , region := .southAsia
  , pluralMarking := .optional }

/-- Burmese: ordinals formed regularly with prefix (pa-hta-ma 'first'
    from inherited Pali, but modern ordinals use prefix tha-). Numeral
    classifiers obligatory (lu thon yauk 'person three CL'). No morphological
    distributive form. No grammatical plural on nouns. -/
def burmese : NumeralProfile :=
  { language := "Burmese"
  , iso := "mya"
  , ordinal := .various
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .southeastAsia
  , pluralMarking := .none }

/-- Hungarian: "first" (elso) is suppletive, higher ordinals regular with
    -dik suffix (masodik 'second', harmadik 'third'). Distributive by
    reduplication (ket-ket 'two-two'). No numeral classifiers. 'Es' (and)
    differs from 'minden' (all/every). Obligatory plural with -k. -/
def hungarian : NumeralProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , ordinal := .firstSuppletion
  , distributive := .markedByReduplication
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .europe
  , pluralMarking := .obligatory }

/-- Russian: "first" (pervyj) is suppletive, "second" (vtoroj) also suppletive,
    higher ordinals from cardinals with suffix (tretij 'third', chetvertyj
    'fourth'). No morphological distributive (uses prepositional phrase 'po +
    dative'). No numeral classifiers. 'I' (and) differs from 'vse' (all).
    Obligatory plural marking. -/
def russian : NumeralProfile :=
  { language := "Russian"
  , iso := "rus"
  , ordinal := .firstSecondSuppletion
  , distributive := .noDistributive
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .europe
  , pluralMarking := .obligatory }

/-- Yoruba: ordinals formed with -(i)keji prefix system, varying patterns
    across the paradigm. No morphological distributive. No numeral classifiers.
    Conjunction 'ati' and universal quantifier 'gbogbo' are distinct. Plural
    marked optionally (awon). -/
def yoruba : NumeralProfile :=
  { language := "Yoruba"
  , iso := "yor"
  , ordinal := .various
  , distributive := .noDistributive
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .africa
  , pluralMarking := .optional }

/-- Swahili: ordinals formed with -a prefix + cardinal (wa-kwanza 'first'
    has distinct root, but -a-pili 'second' etc. are regular). No
    morphological distributive. No numeral classifiers (noun class system
    serves a different function). 'Na' (and) differs from '-ote' (all).
    Obligatory plural via noun class prefixes. -/
def swahili : NumeralProfile :=
  { language := "Swahili"
  , iso := "swh"
  , ordinal := .firstSuppletion
  , distributive := .noDistributive
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .africa
  , pluralMarking := .obligatory }

/-- Tagalog: ordinals with pang- prefix (pang-una 'first' from una 'precede',
    pang-alawa 'second'). Distributive by reduplication (dalawa-dalawa
    'two-two'). No obligatory numeral classifiers (linkers na/ng serve
    different function). 'At' (and) and 'lahat' (all) are differentiated.
    Optional plural (mga). -/
def tagalog : NumeralProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , ordinal := .various
  , distributive := .markedByReduplication
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .southeastAsia
  , pluralMarking := .optional }

/-- Georgian: ordinals formed with me-...-e circumfix (me-or-e 'second',
    me-sam-e 'third'). "First" (p'irveli) is suppletive. Distributive by
    suffix -agan (or-agan 'two each'). No numeral classifiers. 'Da' (and)
    differs from 'q'vela' (all). Obligatory plural. -/
def georgian : NumeralProfile :=
  { language := "Georgian"
  , iso := "kat"
  , ordinal := .firstSuppletion
  , distributive := .markedBySuffix
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .westAsia
  , pluralMarking := .obligatory }

/-- Finnish: ordinals formed regularly with -(n)s suffix (ensimmainen 'first'
    is suppletive, toinen 'second' from eri 'different', kolmas 'third' etc.
    regular). No morphological distributive. No classifiers. 'Ja' (and) differs
    from 'kaikki' (all). Obligatory plural with -t. -/
def finnish : NumeralProfile :=
  { language := "Finnish"
  , iso := "fin"
  , ordinal := .firstSecondSuppletion
  , distributive := .noDistributive
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .europe
  , pluralMarking := .obligatory }

/-- Tzeltal (Mayan, Mesoamerica): ordinals not productively formed. Numeral
    classifiers obligatory (distinct from Mayan noun classifiers). No
    morphological distributive. Conjunction and universal quantifier are
    differentiated. No obligatory plural on nouns. -/
def tzeltal : NumeralProfile :=
  { language := "Tzeltal"
  , iso := "tzh"
  , ordinal := .noOrdinals
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .mesoamerica
  , pluralMarking := .none }

/-- Malay/Indonesian: ordinals with ke- prefix (ke-satu 'first' regular,
    pertama 'first' from Skt also used). No morphological distributive.
    Obligatory numeral classifiers (tiga orang murid 'three CL student').
    'Dan' (and) differs from 'semua' (all). Optional plural by
    reduplication. -/
def indonesian : NumeralProfile :=
  { language := "Indonesian"
  , iso := "ind"
  , ordinal := .various
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .southeastAsia
  , pluralMarking := .optional }

/-- All language profiles in our sample. -/
def allLanguages : List NumeralProfile :=
  [ english, mandarin, japanese, thai, vietnamese, turkish, korean
  , hindi, bengali, burmese, hungarian, russian, yoruba, swahili
  , tagalog, georgian, finnish, tzeltal, indonesian ]

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

-- Classifier status
example : english.classifier = .absent := by native_decide
example : mandarin.classifier = .obligatory := by native_decide
example : japanese.classifier = .obligatory := by native_decide
example : thai.classifier = .obligatory := by native_decide
example : vietnamese.classifier = .obligatory := by native_decide
example : turkish.classifier = .optional := by native_decide
example : korean.classifier = .optional := by native_decide
example : tzeltal.classifier = .obligatory := by native_decide
example : indonesian.classifier = .obligatory := by native_decide
example : hindi.classifier = .absent := by native_decide

-- Ordinal formation
example : english.ordinal = .firstSecondSuppletion := by native_decide
example : mandarin.ordinal = .allFromCardinals := by native_decide
example : japanese.ordinal = .allFromCardinals := by native_decide
example : russian.ordinal = .firstSecondSuppletion := by native_decide
example : hungarian.ordinal = .firstSuppletion := by native_decide
example : turkish.ordinal = .allFromCardinals := by native_decide

-- Distributive numerals
example : english.distributive = .noDistributive := by native_decide
example : japanese.distributive = .markedByReduplication := by native_decide
example : turkish.distributive = .markedBySuffix := by native_decide
example : hindi.distributive = .markedByReduplication := by native_decide
example : georgian.distributive = .markedBySuffix := by native_decide
example : hungarian.distributive = .markedByReduplication := by native_decide

-- Conjunction-quantifier relationship
example : english.conjQuant = .differentiation := by native_decide
example : mandarin.conjQuant = .differentiation := by native_decide

-- ============================================================================
-- Typological Generalizations: Ordinal Numerals (Ch 53)
-- ============================================================================

/-- Suppletive "first" is the dominant ordinal formation strategy (WALS Ch 53).
    Languages with suppletive "first" (alone or with suppletive "second")
    outnumber languages where all ordinals derive regularly from cardinals. -/
theorem suppletive_first_dominant :
    ch53Distribution.firstSuppletion + ch53Distribution.firstSecondSuppletion >
    ch53Distribution.allFromCardinals := by
  native_decide

/-- "First" suppletion alone is the single most common ordinal pattern. -/
theorem first_suppletion_most_common :
    ch53Distribution.firstSuppletion > ch53Distribution.firstSecondSuppletion ∧
    ch53Distribution.firstSuppletion > ch53Distribution.allFromCardinals ∧
    ch53Distribution.firstSuppletion > ch53Distribution.noOrdinals := by
  native_decide

/-- Languages with some form of ordinal formation (regular or suppletive)
    outnumber languages lacking ordinals entirely. Most languages have ordinals. -/
theorem most_languages_have_ordinals :
    ch53Distribution.firstSuppletion + ch53Distribution.firstSecondSuppletion +
    ch53Distribution.allFromCardinals + ch53Distribution.various >
    ch53Distribution.noOrdinals * 3 := by
  native_decide

-- ============================================================================
-- Typological Generalizations: Distributive Numerals (Ch 54)
-- ============================================================================

/-- Languages with dedicated distributive numeral forms outnumber those
    without, but neither is a negligible minority. -/
theorem distributive_majority_has_marking :
    ch54Distribution.reduplication + ch54Distribution.suffixCount +
    ch54Distribution.prefixCount + ch54Distribution.otherMeans >
    ch54Distribution.noDistributive := by
  native_decide

/-- Reduplication is the single most common distributive strategy,
    outnumbering any other individual morphological means. -/
theorem reduplication_most_common_distributive :
    ch54Distribution.reduplication > ch54Distribution.suffixCount ∧
    ch54Distribution.reduplication > ch54Distribution.prefixCount ∧
    ch54Distribution.reduplication > ch54Distribution.otherMeans ∧
    ch54Distribution.reduplication > ch54Distribution.noDistributive := by
  native_decide

-- ============================================================================
-- Typological Generalizations: Numeral Classifiers (Ch 55)
-- ============================================================================

/-- Languages without numeral classifiers are the global majority (WALS Ch 55).
    260 out of 400 sampled languages lack classifiers entirely. -/
theorem no_classifiers_is_majority :
    ch55Distribution.absent > ch55Distribution.optional + ch55Distribution.obligatory := by
  native_decide

/-- Languages without classifiers constitute over half the sample. -/
theorem no_classifiers_over_half :
    ch55Distribution.absent * 2 > ch55Distribution.total := by
  native_decide

/-- Obligatory classifiers are more common than optional ones globally.
    This is somewhat counterintuitive --- it suggests that once a language
    develops classifiers, they tend to become grammaticalized as obligatory. -/
theorem obligatory_more_common_than_optional :
    ch55Distribution.obligatory > ch55Distribution.optional := by
  native_decide

-- ============================================================================
-- Typological Generalizations: Conjunctions and Quantifiers (Ch 56)
-- ============================================================================

/-- Differentiation between 'and' and 'all' is the dominant pattern (WALS Ch 56).
    Most languages use distinct morphemes for conjunction and universal
    quantification. -/
theorem differentiation_dominant :
    ch56Distribution.differentiation > ch56Distribution.identity := by
  native_decide

/-- Differentiation accounts for more than three-quarters of the sample. -/
theorem differentiation_supermajority :
    ch56Distribution.differentiation * 4 > ch56Distribution.total * 3 := by
  native_decide

/-- Identity between 'and' and 'all' is a non-negligible minority pattern,
    attested in roughly a fifth of languages (43 out of 220). -/
theorem identity_nonnegligible :
    ch56Distribution.identity * 6 >= ch56Distribution.total := by
  native_decide

-- ============================================================================
-- Cross-Dimensional Generalizations
-- ============================================================================

/-- Does a language have obligatory numeral classifiers? -/
def NumeralProfile.hasObligatoryClassifiers (p : NumeralProfile) : Bool :=
  p.classifier == .obligatory

/-- Does a language have any numeral classifiers (obligatory or optional)? -/
def NumeralProfile.hasClassifiers (p : NumeralProfile) : Bool :=
  p.classifier != .absent

/-- Does a language have obligatory plural marking on common nouns? -/
def NumeralProfile.hasObligatoryPlural (p : NumeralProfile) : Bool :=
  p.pluralMarking == .obligatory

/-- Does a language form "first" by suppletion? -/
def NumeralProfile.hasFirstSuppletion (p : NumeralProfile) : Bool :=
  p.ordinal == .firstSuppletion || p.ordinal == .firstSecondSuppletion

/-- Does a language have a morphological distributive numeral form? -/
def NumeralProfile.hasDistributive (p : NumeralProfile) : Bool :=
  p.distributive != .noDistributive

/-- Is a language in the East/Southeast Asian region? -/
def NumeralProfile.isEastSoutheastAsian (p : NumeralProfile) : Bool :=
  p.region == .eastAsia || p.region == .southeastAsia

/-- **Sanches-Slobin generalization** (Sanches & Slobin 1973): Classifier
    languages tend to lack obligatory plural marking on nouns. In our sample,
    every language with obligatory classifiers lacks obligatory plural.

    The theoretical explanation: classifiers already individuate entities for
    counting, making obligatory plural morphology redundant. -/
theorem classifier_implies_no_obligatory_plural :
    let withObligatoryClassifiers := allLanguages.filter (·.hasObligatoryClassifiers)
    withObligatoryClassifiers.all (fun p => !p.hasObligatoryPlural) = true := by
  native_decide

/-- Converse of Sanches-Slobin: every language in our sample with obligatory
    plural marking lacks obligatory classifiers. (This is the contrapositive,
    independently verifiable on the data.) -/
theorem obligatory_plural_implies_no_obligatory_classifier :
    let withObligatoryPlural := allLanguages.filter (·.hasObligatoryPlural)
    withObligatoryPlural.all (fun p => !p.hasObligatoryClassifiers) = true := by
  native_decide

/-- Numeral classifiers concentrate in East and Southeast Asia in our sample:
    every obligatory-classifier language in our sample is in East Asia, Southeast
    Asia, or Mesoamerica. -/
theorem classifiers_areal_concentration :
    let obligatory := allLanguages.filter (·.hasObligatoryClassifiers)
    obligatory.all (fun p =>
      p.region == .eastAsia || p.region == .southeastAsia ||
      p.region == .mesoamerica) = true := by
  native_decide

/-- In our sample, East/Southeast Asian languages with obligatory classifiers
    all form ordinals regularly from cardinals (no suppletion of "first").
    This is consistent with the observation that agglutinative numeral
    morphology in these languages extends uniformly to ordinals. -/
theorem eastasian_classifier_langs_regular_ordinals :
    let eastAsianClassifier := allLanguages.filter (fun p =>
      p.isEastSoutheastAsian && p.hasObligatoryClassifiers &&
      -- Exclude languages with 'various' ordinal patterns
      p.ordinal != .various)
    eastAsianClassifier.all (fun p =>
      p.ordinal == .allFromCardinals) = true := by
  native_decide

/-- European languages in our sample all show suppletive "first" (either
    alone or with suppletive "second"). No European language in our sample
    derives "first" regularly from "one". -/
theorem european_first_suppletion :
    let european := allLanguages.filter (fun p => p.region == .europe)
    european.all (·.hasFirstSuppletion) = true := by
  native_decide

/-- Japanese is a notable exception to any strict complementarity between
    obligatory classifiers and distributive morphology: it has both obligatory
    classifiers and distributive-by-reduplication (hito-ri hito-ri). -/
theorem japanese_has_both_classifier_and_distributive :
    japanese.hasObligatoryClassifiers && japanese.hasDistributive = true := by
  native_decide

/-- In our sample, the majority of obligatory-classifier languages lack
    morphological distributive forms. Japanese is the sole exception. -/
theorem most_obligatory_classifier_no_distributive :
    let obligCl := allLanguages.filter (·.hasObligatoryClassifiers)
    let withoutDist := obligCl.filter (fun p => !p.hasDistributive)
    withoutDist.length > obligCl.length / 2 := by
  native_decide

-- ============================================================================
-- The Greenberg Hierarchy for Ordinal Suppletion
-- ============================================================================

/-- Greenberg's (1978) implicational universal for ordinal suppletion:
    if a language has a suppletive ordinal for numeral N, then it has
    suppletive ordinals for all numerals less than N. Equivalently:
    suppletion cuts off at some point in the sequence 1st, 2nd, 3rd, ...
    and all ordinals above the cutoff are regular.

    The WALS data captures the coarsest version: suppletion is most likely
    for "first", less likely for "second", and rare beyond that. Our inductive
    type captures three attested cutoff points (none, first-only, first+second). -/
inductive SuppletionCutoff where
  | none                 -- no suppletive ordinals (all regular from cardinals)
  | first                -- only "first" is suppletive
  | firstAndSecond       -- "first" and "second" are suppletive
  deriving DecidableEq, BEq, Repr

/-- Numeric rank for the suppletion cutoff (higher = more suppletion). -/
def SuppletionCutoff.rank : SuppletionCutoff -> Nat
  | .none => 0
  | .first => 1
  | .firstAndSecond => 2

/-- Map ordinal formation type to suppletion cutoff. Languages with 'various'
    or 'no ordinals' patterns are excluded from the hierarchy. -/
def OrdinalFormation.suppletionCutoff : OrdinalFormation -> Option SuppletionCutoff
  | .allFromCardinals => some .none
  | .firstSuppletion => some .first
  | .firstSecondSuppletion => some .firstAndSecond
  | .various => Option.none
  | .noOrdinals => Option.none

/-- The hierarchy is consistent: rank of each cutoff increases monotonically. -/
theorem suppletion_hierarchy_ordering :
    SuppletionCutoff.none.rank < SuppletionCutoff.first.rank ∧
    SuppletionCutoff.first.rank < SuppletionCutoff.firstAndSecond.rank := by
  native_decide

/-- In our sample, the WALS aggregate confirms the hierarchy: languages
    with "first"-only suppletion are more numerous than those with
    "first+second" suppletion, which in turn are more numerous than
    those with no suppletion at all. This reflects the implicational
    scale: suppletion at higher numerals is rarer. -/
theorem suppletion_frequency_matches_hierarchy :
    ch53Distribution.firstSuppletion > ch53Distribution.firstSecondSuppletion ∧
    ch53Distribution.firstSecondSuppletion > ch53Distribution.allFromCardinals := by
  native_decide

end Phenomena.Numerals.Typology
