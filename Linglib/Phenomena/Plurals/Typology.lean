import Linglib.Core.Lexical.Word
import Linglib.Features.Prominence
import Linglib.Datasets.WALS.Features.F33A
import Linglib.Datasets.WALS.Features.F34A
import Linglib.Datasets.WALS.Features.F35A
import Linglib.Datasets.WALS.Features.F36A

/-!
# Cross-Linguistic Typology of Nominal Plurality (WALS Chapters 33--36)
@cite{corbett-2000} @cite{dryer-haspelmath-2013} @cite{haspelmath-2013}

Typological data on how languages encode plurality, drawn from four WALS
chapters by Dryer, Haspelmath, Daniel, and Moravcsik. The data covers four
dimensions of plural morphology and syntax:

1. **Coding of Nominal Plurality** (Ch 33, Dryer): How languages mark plural
   on nouns --- suffix, prefix, stem change, tone, reduplication, plural word,
   clitic, mixed morphological, or no marking at all. Suffixing dominates
   (495/957 languages), followed by plural words (150) and plural prefixes (118).

2. **Occurrence of Nominal Plurality** (Ch 34, Haspelmath): When plural marking
   is used. The crucial dimension is the interaction of animacy and obligatoriness:
   plural marking may be obligatory on all nouns, restricted to human nouns, or
   absent entirely. An implicational hierarchy governs this: if a language marks
   plural on inanimate nouns, it also marks plural on human nouns (never the
   reverse).

3. **Plurality in Independent Personal Pronouns** (Ch 35, Daniel): How pronouns
   encode number. The dominant pattern (114/260) is person-number stems (e.g.
   English I/we), where number is fused into the lexical root. Affix-based number
   on pronouns is rarer and may use either pronominal or nominal affixes.

4. **The Associative Plural** (Ch 36, Daniel & Moravcsik): "Tanaka and
   associates" constructions. 200/237 sampled languages have some form of
   associative plural. In nearly half (104), the associative marker is the same
   morpheme used for additive (ordinary) plurals.

-/

namespace Phenomena.Plurals.Typology

-- ============================================================================
-- Chapter 33: Coding of Nominal Plurality (Dryer)
-- ============================================================================

/-- How a language morphologically codes plurality on nouns (WALS Ch 33).

    The nine categories distinguish morphological strategies (prefix, suffix,
    stem change, tone, reduplication, mixed) from phrasal strategies (plural
    word, clitic) and from the absence of any plural marking. -/
inductive PluralCoding where
  | prefix           -- plural prefix (e.g. Swahili wa-toto 'children')
  | suffix           -- plural suffix (e.g. English dog-s)
  | stemChange       -- stem-internal vowel change (e.g. Maricopa humar/humaar)
  | tone             -- tonal change (e.g. Ngiti kamà/kámá 'chief/chiefs')
  | reduplication     -- complete reduplication (e.g. Indonesian rumah-rumah)
  | mixedMorphological -- two or more methods, none primary (e.g. Arabic)
  | pluralWord       -- separate word in NP (e.g. Hawaiian mau, Mandarin 些)
  | pluralClitic     -- NP-level clitic (e.g. Cayuvava me=)
  | noPlural         -- no indication of plurality
  deriving DecidableEq, Repr

/-- WALS Chapter 33 distribution: language counts per plural coding strategy.
    Total: 957 languages. -/
structure PluralCodingDistribution where
  prefixCount : Nat
  suffixCount : Nat
  stemChange : Nat
  tone : Nat
  reduplication : Nat
  mixedMorphological : Nat
  pluralWord : Nat
  pluralClitic : Nat
  noPlural : Nat
  deriving Repr

def PluralCodingDistribution.total (d : PluralCodingDistribution) : Nat :=
  d.prefixCount + d.suffixCount + d.stemChange + d.tone + d.reduplication +
  d.mixedMorphological + d.pluralWord + d.pluralClitic + d.noPlural

/-- Actual WALS Ch 33 counts. -/
def ch33Distribution : PluralCodingDistribution :=
  { prefixCount := 118
  , suffixCount := 495
  , stemChange := 5
  , tone := 2
  , reduplication := 8
  , mixedMorphological := 34
  , pluralWord := 150
  , pluralClitic := 59
  , noPlural := 86 }

-- ============================================================================
-- Chapter 34: Occurrence of Nominal Plurality (Haspelmath)
-- ============================================================================

/-- When plural marking occurs on full nouns (WALS Ch 34).

    The six values cross two dimensions: animacy scope (none / human-only / all)
    and obligatoriness (optional / obligatory). An implicational hierarchy holds:
    if inanimate nouns are marked, human nouns are too (never the reverse). -/
inductive PluralOccurrence where
  | noNominalPlural            -- no nominal plural at all
  | humanOnlyOptional          -- plural only on human nouns, optional
  | humanOnlyObligatory        -- plural only on human nouns, obligatory
  | allNounsAlwaysOptional     -- plural on all nouns, always optional
  | allNounsOptionalInanimates -- plural on all nouns, obligatory for human, optional for inanimate
  | allNounsAlwaysObligatory   -- plural on all nouns, always obligatory
  deriving DecidableEq, Repr

/-- WALS Chapter 34 distribution: language counts per occurrence type.
    Total: 290 languages. -/
structure PluralOccurrenceDistribution where
  noNominalPlural : Nat
  humanOnlyOptional : Nat
  humanOnlyObligatory : Nat
  allNounsAlwaysOptional : Nat
  allNounsOptionalInanimates : Nat
  allNounsAlwaysObligatory : Nat
  deriving Repr

def PluralOccurrenceDistribution.total (d : PluralOccurrenceDistribution) : Nat :=
  d.noNominalPlural + d.humanOnlyOptional + d.humanOnlyObligatory +
  d.allNounsAlwaysOptional + d.allNounsOptionalInanimates + d.allNounsAlwaysObligatory

/-- Actual WALS Ch 34 counts. -/
def ch34Distribution : PluralOccurrenceDistribution :=
  { noNominalPlural := 28
  , humanOnlyOptional := 20
  , humanOnlyObligatory := 39
  , allNounsAlwaysOptional := 55
  , allNounsOptionalInanimates := 15
  , allNounsAlwaysObligatory := 133 }

-- ============================================================================
-- Chapter 35: Plurality in Independent Personal Pronouns (Daniel)
-- ============================================================================

/-- How independent personal pronouns encode number (WALS Ch 35).

    The key typological variable is whether number is expressed in the stem,
    an affix, or both, and whether the affix is shared with nouns. -/
inductive PronounPlurality where
  | noIndependentPronouns       -- no independent subject pronouns (e.g. Acoma)
  | numberIndifferent           -- same form for sg and pl (e.g. Piraha ti 'I/we')
  | personNumberAffixes         -- both person and number are affixal
  | personNumberStem            -- person+number fused in stem (e.g. Dogon mi/emme)
  | pnStemPronominalAffix       -- person-number stem + pronominal plural affix
  | pnStemNominalAffix          -- person-number stem + nominal plural affix (e.g. Russian)
  | personStemPronominalAffix   -- person stem + pronominal plural affix (e.g. Chuvash)
  | personStemNominalAffix      -- person stem + nominal plural affix (e.g. Mandarin -men)
  deriving DecidableEq, Repr

/-- WALS Chapter 35 distribution: language counts per pronoun plurality type.
    Total: 260 languages. -/
structure PronounPluralityDistribution where
  noIndependentPronouns : Nat
  numberIndifferent : Nat
  personNumberAffixes : Nat
  personNumberStem : Nat
  pnStemPronominalAffix : Nat
  pnStemNominalAffix : Nat
  personStemPronominalAffix : Nat
  personStemNominalAffix : Nat
  deriving Repr

def PronounPluralityDistribution.total (d : PronounPluralityDistribution) : Nat :=
  d.noIndependentPronouns + d.numberIndifferent + d.personNumberAffixes +
  d.personNumberStem + d.pnStemPronominalAffix + d.pnStemNominalAffix +
  d.personStemPronominalAffix + d.personStemNominalAffix

/-- Actual WALS Ch 35 counts. -/
def ch35Distribution : PronounPluralityDistribution :=
  { noIndependentPronouns := 2
  , numberIndifferent := 8
  , personNumberAffixes := 25
  , personNumberStem := 114
  , pnStemPronominalAffix := 47
  , pnStemNominalAffix := 22
  , personStemPronominalAffix := 23
  , personStemNominalAffix := 19 }

-- ============================================================================
-- Chapter 36: The Associative Plural (Daniel & Moravcsik)
-- ============================================================================

/-- Type of associative plural marking (WALS Ch 36).

    Associative plurals are "X and associates" constructions (e.g. Japanese
    Tanaka-tachi 'Tanaka and his group'). The typological split is between
    languages where the associative marker overlaps with the additive (ordinary)
    plural marker vs. languages with a dedicated associative form. -/
inductive AssociativePlural where
  | sameAsAdditive      -- marker also used for additive plural (e.g. Zulu, Turkish)
  | uniqueAffixal       -- dedicated affix (e.g. Hungarian -ek)
  | uniquePeriphrastic  -- dedicated free/clitic marker (e.g. Tagalog, Japanese -tachi)
  | absent              -- no productive associative plural (e.g. Russian, English)
  deriving DecidableEq, Repr

/-- WALS Chapter 36 distribution: language counts per associative plural type.
    Total: 237 languages. -/
structure AssociativePluralDistribution where
  sameAsAdditive : Nat
  uniqueAffixal : Nat
  uniquePeriphrastic : Nat
  absent : Nat
  deriving Repr

def AssociativePluralDistribution.total (d : AssociativePluralDistribution) : Nat :=
  d.sameAsAdditive + d.uniqueAffixal + d.uniquePeriphrastic + d.absent

/-- Actual WALS Ch 36 counts. -/
def ch36Distribution : AssociativePluralDistribution :=
  { sameAsAdditive := 104
  , uniqueAffixal := 48
  , uniquePeriphrastic := 48
  , absent := 37 }

-- ============================================================================
-- Distribution Verification
-- ============================================================================

/-- Ch 33 total: 957 languages. -/
example : ch33Distribution.total = 957 := by native_decide

/-- Ch 34 total: 290 languages. -/
example : ch34Distribution.total = 290 := by native_decide

/-- Ch 35 total: 260 languages. -/
example : ch35Distribution.total = 260 := by native_decide

/-- Ch 36 total: 237 languages. -/
example : ch36Distribution.total = 237 := by native_decide

-- ============================================================================
-- Language Profiles
-- ============================================================================

/-- A language's plurality profile across all four WALS dimensions. -/
structure PluralityProfile where
  language : String
  /-- ISO 639-3 code -/
  iso : String
  /-- Ch 33: How plurality is coded on nouns -/
  coding : PluralCoding
  /-- Ch 34: When plural marking occurs -/
  occurrence : PluralOccurrence
  /-- Ch 35: Pronoun plurality type -/
  pronounPlurality : PronounPlurality
  /-- Ch 36: Associative plural -/
  associativePlural : AssociativePlural
  deriving Repr, DecidableEq

-- ============================================================================
-- Language Instances
-- ============================================================================

/-- English: suffix plural (-s), obligatory on all nouns, person-number stems
    in pronouns (I/we, you/you), no productive associative plural. -/
def english : PluralityProfile :=
  { language := "English"
  , iso := "eng"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .absent }

/-- Mandarin Chinese: no morphological plural on nouns (bare nouns are number-
    neutral), person stem + nominal plural affix -men on pronouns
    (wo/wo-men 'I/we'), associative plural uses same -men marker. -/
def mandarin : PluralityProfile :=
  { language := "Mandarin"
  , iso := "cmn"
  , coding := .noPlural
  , occurrence := .noNominalPlural
  , pronounPlurality := .personStemNominalAffix
  , associativePlural := .sameAsAdditive }

/-- Japanese: no morphological plural on common nouns, plural on all nouns
    is always optional (suffix -tachi limited, and optional), person-number
    stems in pronouns, unique periphrastic associative plural (-tachi on
    proper names: Tanaka-tachi). -/
def japanese : PluralityProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , coding := .noPlural
  , occurrence := .noNominalPlural
  , pronounPlurality := .personNumberStem
  , associativePlural := .uniquePeriphrastic }

/-- Turkish: suffix plural (-ler, -lar with vowel harmony), obligatory on
    all nouns (except after numerals), person stem + nominal plural affix
    on pronouns (ben vs biz, sen vs siz, but -ler suffix also used),
    associative plural uses same -ler marker (Ali-ler 'Ali and associates'). -/
def turkish : PluralityProfile :=
  { language := "Turkish"
  , iso := "tur"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

/-- Finnish: suffix plural (-t nominative, -i- oblique), obligatory on all
    nouns, person-number stem + pronominal affix in pronouns (mina/me),
    no productive associative plural. -/
def finnish : PluralityProfile :=
  { language := "Finnish"
  , iso := "fin"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .pnStemPronominalAffix
  , associativePlural := .absent }

/-- Arabic (Standard): mixed morphological plural --- both suffixation
    (-aat, -uun) and "broken" stem-internal changes are productive, neither
    is clearly primary. Obligatory on all nouns. Person-number stem in
    pronouns (ana/nahnu). Associative plural same as additive. -/
def arabic : PluralityProfile :=
  { language := "Arabic"
  , iso := "arb"
  , coding := .mixedMorphological
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

/-- Hungarian: suffix plural (-k), obligatory on all nouns, person-number
    stem + nominal plural affix on pronouns (en vs mi, with -k also on nouns),
    unique affixal associative plural (-ek: Pal-ek 'Paul and associates',
    distinct from additive -k or -ak). -/
def hungarian : PluralityProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .pnStemNominalAffix
  , associativePlural := .uniqueAffixal }

/-- Swahili: plural marked by noun class prefixes (wa-, vi-, mi-, ma-),
    obligatory on all nouns, person-number stems in pronouns (mimi/sisi),
    no productive associative plural. -/
def swahili : PluralityProfile :=
  { language := "Swahili"
  , iso := "swh"
  , coding := .prefix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .absent }

/-- Indonesian: complete reduplication (rumah-rumah 'houses'), plural marking
    optional on all nouns. Person-number stems in pronouns (saya/kami).
    No productive associative plural. -/
def indonesian : PluralityProfile :=
  { language := "Indonesian"
  , iso := "ind"
  , coding := .reduplication
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .absent }

/-- Hindi: suffix plural (-e, -en, -iya), obligatory on all nouns,
    person-number stems in pronouns (mai vs ham), associative plural uses
    same plural marker (Sharma-log 'Sharma and family'). -/
def hindi : PluralityProfile :=
  { language := "Hindi"
  , iso := "hin"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

/-- Korean: suffix plural (-tul), optional on all nouns (number-neutral bare
    forms are common), person-number stems in pronouns (na/uri),
    associative plural uses same -tul marker. -/
def korean : PluralityProfile :=
  { language := "Korean"
  , iso := "kor"
  , coding := .suffix
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

/-- Tagalog: plural word (mga, prenominal), optional on all nouns,
    person-number stems in pronouns (ako/kami/tayo), unique periphrastic
    associative plural (sina: sina Pedro 'Pedro and associates'). -/
def tagalog : PluralityProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , coding := .pluralWord
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .uniquePeriphrastic }

/-- Russian: suffix plural (-y, -i, -a), obligatory on all nouns,
    person-number stem + nominal plural affix in pronouns (ja vs m-y),
    no productive associative plural. -/
def russian : PluralityProfile :=
  { language := "Russian"
  , iso := "rus"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .pnStemNominalAffix
  , associativePlural := .absent }

/-- Zulu (Bantu): prefix plural (class prefixes: umu-ntu/aba-ntu),
    obligatory on all nouns, person-number stems in pronouns,
    associative plural uses same prefix system (o-Faku 'Faku and company'). -/
def zulu : PluralityProfile :=
  { language := "Zulu"
  , iso := "zul"
  , coding := .prefix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

/-- Hawaiian: plural word (mau, prenominal), optional on all nouns,
    person-number stems in pronouns, associative plural absent. -/
def hawaiian : PluralityProfile :=
  { language := "Hawaiian"
  , iso := "haw"
  , coding := .pluralWord
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .absent }

/-- Lezgian (Daghestanian): suffix plural (-ar, -er), obligatory on all
    nouns (but absent with numerals), person-number stems in pronouns,
    associative plural uses same suffix. -/
def lezgian : PluralityProfile :=
  { language := "Lezgian"
  , iso := "lez"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

/-- All language profiles in our sample. -/
def allLanguages : List PluralityProfile :=
  [ english, mandarin, japanese, turkish, finnish, arabic, hungarian
  , swahili, indonesian, hindi, korean, tagalog, russian, zulu
  , hawaiian, lezgian ]

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

-- Coding
example : english.coding = .suffix := by native_decide
example : mandarin.coding = .noPlural := by native_decide
example : japanese.coding = .noPlural := by native_decide
example : turkish.coding = .suffix := by native_decide
example : swahili.coding = .prefix := by native_decide
example : indonesian.coding = .reduplication := by native_decide
example : arabic.coding = .mixedMorphological := by native_decide
example : hungarian.coding = .suffix := by native_decide
example : tagalog.coding = .pluralWord := by native_decide
example : zulu.coding = .prefix := by native_decide

-- Occurrence
example : english.occurrence = .allNounsAlwaysObligatory := by native_decide
example : mandarin.occurrence = .noNominalPlural := by native_decide
example : korean.occurrence = .allNounsAlwaysOptional := by native_decide
example : indonesian.occurrence = .allNounsAlwaysOptional := by native_decide

-- Pronouns
example : mandarin.pronounPlurality = .personStemNominalAffix := by native_decide
example : russian.pronounPlurality = .pnStemNominalAffix := by native_decide
example : finnish.pronounPlurality = .pnStemPronominalAffix := by native_decide

-- Associative plural
example : hungarian.associativePlural = .uniqueAffixal := by native_decide
example : japanese.associativePlural = .uniquePeriphrastic := by native_decide
example : turkish.associativePlural = .sameAsAdditive := by native_decide
example : english.associativePlural = .absent := by native_decide

-- ============================================================================
-- Typological Generalizations
-- ============================================================================

/-- Suffixing is the dominant plural marking strategy (WALS Ch 33).
    Plural suffixes (495) outnumber every other single strategy. -/
theorem suffixing_dominant :
    ch33Distribution.suffixCount > ch33Distribution.prefixCount ∧
    ch33Distribution.suffixCount > ch33Distribution.pluralWord ∧
    ch33Distribution.suffixCount > ch33Distribution.pluralClitic ∧
    ch33Distribution.suffixCount > ch33Distribution.noPlural ∧
    ch33Distribution.suffixCount > ch33Distribution.mixedMorphological ∧
    ch33Distribution.suffixCount > ch33Distribution.stemChange ∧
    ch33Distribution.suffixCount > ch33Distribution.tone ∧
    ch33Distribution.suffixCount > ch33Distribution.reduplication := by
  native_decide

/-- Over half of all sampled languages use plural suffixes. -/
theorem suffixing_is_majority :
    ch33Distribution.suffixCount * 2 > ch33Distribution.total := by
  native_decide

/-- Obligatory marking on all nouns is the most common occurrence pattern
    (WALS Ch 34): 133 out of 290 languages. -/
theorem obligatory_all_most_common :
    ch34Distribution.allNounsAlwaysObligatory > ch34Distribution.noNominalPlural ∧
    ch34Distribution.allNounsAlwaysObligatory > ch34Distribution.humanOnlyOptional ∧
    ch34Distribution.allNounsAlwaysObligatory > ch34Distribution.humanOnlyObligatory ∧
    ch34Distribution.allNounsAlwaysObligatory > ch34Distribution.allNounsAlwaysOptional ∧
    ch34Distribution.allNounsAlwaysObligatory > ch34Distribution.allNounsOptionalInanimates := by
  native_decide

/-- The animacy hierarchy for nominal plurality (Haspelmath, Ch 34):
    human nouns are more likely to have plural marking than inanimates.
    In the WALS sample, no language has plural only on inanimates ---
    the three logically possible "inanimate-only" types are unattested.
    This is captured here as: languages with human-only plural (59)
    outnumber any hypothetical inanimate-only count (0). -/
theorem animacy_hierarchy_human_over_inanimate :
    ch34Distribution.humanOnlyOptional + ch34Distribution.humanOnlyObligatory > 0 := by
  native_decide

/-- Person-number stems dominate pronoun plurality (WALS Ch 35).
    114/260 languages fuse person and number into an unanalysable stem
    (e.g. English I/we, Dogon mi/emme). This is the single largest
    category, larger than any other individual type. -/
theorem person_number_stem_dominant :
    ch35Distribution.personNumberStem > ch35Distribution.personNumberAffixes ∧
    ch35Distribution.personNumberStem > ch35Distribution.pnStemPronominalAffix ∧
    ch35Distribution.personNumberStem > ch35Distribution.pnStemNominalAffix ∧
    ch35Distribution.personNumberStem > ch35Distribution.personStemPronominalAffix ∧
    ch35Distribution.personNumberStem > ch35Distribution.personStemNominalAffix ∧
    ch35Distribution.personNumberStem > ch35Distribution.numberIndifferent ∧
    ch35Distribution.personNumberStem > ch35Distribution.noIndependentPronouns := by
  native_decide

/-- Nearly all languages distinguish number in pronouns: only 10/260
    languages lack number distinctions in independent personal pronouns
    (2 with no independent pronouns + 8 number-indifferent). -/
theorem pronoun_number_near_universal :
    ch35Distribution.noIndependentPronouns + ch35Distribution.numberIndifferent < 15 ∧
    ch35Distribution.total -
      (ch35Distribution.noIndependentPronouns + ch35Distribution.numberIndifferent) > 240 := by
  native_decide

/-- Associative plurals are widespread: 200/237 sampled languages have
    some form of associative plural (only 37 lack them entirely). -/
theorem associative_plural_widespread :
    ch36Distribution.sameAsAdditive + ch36Distribution.uniqueAffixal +
      ch36Distribution.uniquePeriphrastic > ch36Distribution.absent * 5 := by
  native_decide

/-- In nearly half of languages with associative plurals, the associative
    marker overlaps with the additive plural marker (104/200 languages
    with associative plurals). -/
theorem associative_often_overlaps_additive :
    ch36Distribution.sameAsAdditive * 2 >=
      ch36Distribution.uniqueAffixal + ch36Distribution.uniquePeriphrastic := by
  native_decide

-- ============================================================================
-- Cross-Dimensional Generalizations
-- ============================================================================

/-- Does a language have morphological plural marking on nouns? -/
def PluralityProfile.hasMorphologicalPlural (p : PluralityProfile) : Bool :=
  p.coding != .noPlural && p.coding != .pluralWord && p.coding != .pluralClitic

/-- Does a language have obligatory plural marking on all nouns? -/
def PluralityProfile.hasObligatoryPlural (p : PluralityProfile) : Bool :=
  p.occurrence == .allNounsAlwaysObligatory ||
  p.occurrence == .allNounsOptionalInanimates

/-- Does a language distinguish number in pronouns? -/
def PluralityProfile.pronounsDistinguishNumber (p : PluralityProfile) : Bool :=
  p.pronounPlurality != .noIndependentPronouns &&
  p.pronounPlurality != .numberIndifferent

/-- In our sample: every language that lacks nominal plural marking still
    distinguishes number in its pronouns.

    This instantiates the hierarchy: pronouns > nouns for number marking. -/
theorem pronouns_mark_number_even_without_nominal_plural :
    let noNominal := allLanguages.filter fun p => p.coding == .noPlural
    noNominal.all (·.pronounsDistinguishNumber) = true := by
  native_decide

/-- In our sample: every language with obligatory plural on all nouns
    also has morphological (affixal) plural marking --- obligatory
    marking implies the language has developed a morphological strategy,
    not just a plural word or clitic. -/
theorem obligatory_implies_morphological :
    let obligatory := allLanguages.filter (·.hasObligatoryPlural)
    obligatory.all (·.hasMorphologicalPlural) = true := by
  native_decide

/-- In our sample: all 16 languages distinguish number in pronouns.
    This is consistent with the near-universality seen in the full
    WALS sample (250/260). -/
theorem all_sample_pronouns_distinguish_number :
    allLanguages.all (·.pronounsDistinguishNumber) = true := by
  native_decide

open Features.Prominence (AnimacyRank)

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

private def fromWALS33A : Datasets.WALS.F33A.PluralityCoding → PluralCoding
  | .pluralPrefix => .prefix
  | .pluralSuffix => .suffix
  | .pluralStemChange => .stemChange
  | .pluralTone => .tone
  | .pluralCompleteReduplication => .reduplication
  | .mixedMorphologicalPlural => .mixedMorphological
  | .pluralWord => .pluralWord
  | .pluralClitic => .pluralClitic
  | .noPlural => .noPlural

private def fromWALS34A : Datasets.WALS.F34A.PluralityOccurrence → PluralOccurrence
  | .noNominalPlural => .noNominalPlural
  | .onlyHumanNounsOptional => .humanOnlyOptional
  | .onlyHumanNounsObligatory => .humanOnlyObligatory
  | .allNounsAlwaysOptional => .allNounsAlwaysOptional
  | .allNounsOptionalInInanimates => .allNounsOptionalInanimates
  | .allNounsAlwaysObligatory => .allNounsAlwaysObligatory

private def fromWALS35A : Datasets.WALS.F35A.PronounPlurality → PronounPlurality
  | .noIndependentSubjectPronouns => .noIndependentPronouns
  | .numberIndifferentPronouns => .numberIndifferent
  | .personNumberAffixes => .personNumberAffixes
  | .personNumberStem => .personNumberStem
  | .personNumberStemPronominalPluralAffix => .pnStemPronominalAffix
  | .personNumberStemNominalPluralAffix => .pnStemNominalAffix
  | .personStemPronominalPluralAffix => .personStemPronominalAffix
  | .personStemNominalPluralAffix => .personStemNominalAffix

private def fromWALS36A : Datasets.WALS.F36A.AssociativePlural → AssociativePlural
  | .associativeSameAsAdditivePlural => .sameAsAdditive
  | .uniqueAffixalAssociativePlural => .uniqueAffixal
  | .uniquePeriphrasticAssociativePlural => .uniquePeriphrastic
  | .noAssociativePlural => .absent

-- ============================================================================
-- WALS Distribution Data (from generated modules)
-- ============================================================================

private abbrev ch33 := Datasets.WALS.F33A.allData
private abbrev ch34 := Datasets.WALS.F34A.allData
private abbrev ch35 := Datasets.WALS.F35A.allData
private abbrev ch36 := Datasets.WALS.F36A.allData

theorem ch33_total : ch33.length = 1066 := by native_decide
theorem ch34_total : ch34.length = 291 := by native_decide
theorem ch35_total : ch35.length = 261 := by native_decide
theorem ch36_total : ch36.length = 236 := by native_decide

-- ============================================================================
-- WALS Grounding: Ch 33 (Coding of Nominal Plurality)
-- ============================================================================

-- Languages where WALS Ch 33 agrees with the hand-coded profile:
-- english, turkish, finnish, arabic (Egyptian), hungarian, swahili,
-- indonesian, hindi, korean, tagalog, russian, zulu, hawaiian, lezgian.
-- Mandarin and Japanese diverge: WALS codes them as pluralSuffix (counting
-- the -men/-tachi suffix on pronouns/nouns), while the profile codes them
-- as noPlural (focusing on common nouns).

theorem english_ch33 :
    (Datasets.WALS.F33A.lookup "eng").map (fromWALS33A ·.value) = some english.coding := by
  native_decide

theorem turkish_ch33 :
    (Datasets.WALS.F33A.lookup "tur").map (fromWALS33A ·.value) = some turkish.coding := by
  native_decide

theorem finnish_ch33 :
    (Datasets.WALS.F33A.lookup "fin").map (fromWALS33A ·.value) = some finnish.coding := by
  native_decide

theorem arabic_ch33 :
    (Datasets.WALS.F33A.lookup "aeg").map (fromWALS33A ·.value) = some arabic.coding := by
  native_decide

theorem hungarian_ch33 :
    (Datasets.WALS.F33A.lookup "hun").map (fromWALS33A ·.value) = some hungarian.coding := by
  native_decide

theorem swahili_ch33 :
    (Datasets.WALS.F33A.lookup "swa").map (fromWALS33A ·.value) = some swahili.coding := by
  native_decide

theorem indonesian_ch33 :
    (Datasets.WALS.F33A.lookup "ind").map (fromWALS33A ·.value) = some indonesian.coding := by
  native_decide

theorem hindi_ch33 :
    (Datasets.WALS.F33A.lookup "hin").map (fromWALS33A ·.value) = some hindi.coding := by
  native_decide

theorem korean_ch33 :
    (Datasets.WALS.F33A.lookup "kor").map (fromWALS33A ·.value) = some korean.coding := by
  native_decide

theorem tagalog_ch33 :
    (Datasets.WALS.F33A.lookup "tag").map (fromWALS33A ·.value) = some tagalog.coding := by
  native_decide

theorem russian_ch33 :
    (Datasets.WALS.F33A.lookup "rus").map (fromWALS33A ·.value) = some russian.coding := by
  native_decide

theorem zulu_ch33 :
    (Datasets.WALS.F33A.lookup "zul").map (fromWALS33A ·.value) = some zulu.coding := by
  native_decide

theorem hawaiian_ch33 :
    (Datasets.WALS.F33A.lookup "haw").map (fromWALS33A ·.value) = some hawaiian.coding := by
  native_decide

theorem lezgian_ch33 :
    (Datasets.WALS.F33A.lookup "lez").map (fromWALS33A ·.value) = some lezgian.coding := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 34 (Occurrence of Nominal Plurality)
-- ============================================================================

-- Languages where WALS Ch 34 agrees with the hand-coded profile.
-- Korean and Hawaiian are absent from the WALS Ch 34 sample.
-- Mandarin and Japanese diverge: WALS codes them as onlyHumanNounsOptional,
-- while the profile codes them as noNominalPlural.

theorem english_ch34 :
    (Datasets.WALS.F34A.lookup "eng").map (fromWALS34A ·.value) = some english.occurrence := by
  native_decide

theorem turkish_ch34 :
    (Datasets.WALS.F34A.lookup "tur").map (fromWALS34A ·.value) = some turkish.occurrence := by
  native_decide

theorem finnish_ch34 :
    (Datasets.WALS.F34A.lookup "fin").map (fromWALS34A ·.value) = some finnish.occurrence := by
  native_decide

theorem arabic_ch34 :
    (Datasets.WALS.F34A.lookup "aeg").map (fromWALS34A ·.value) = some arabic.occurrence := by
  native_decide

theorem hungarian_ch34 :
    (Datasets.WALS.F34A.lookup "hun").map (fromWALS34A ·.value) = some hungarian.occurrence := by
  native_decide

theorem swahili_ch34 :
    (Datasets.WALS.F34A.lookup "swa").map (fromWALS34A ·.value) = some swahili.occurrence := by
  native_decide

theorem indonesian_ch34 :
    (Datasets.WALS.F34A.lookup "ind").map (fromWALS34A ·.value) = some indonesian.occurrence := by
  native_decide

theorem hindi_ch34 :
    (Datasets.WALS.F34A.lookup "hin").map (fromWALS34A ·.value) = some hindi.occurrence := by
  native_decide

theorem tagalog_ch34 :
    (Datasets.WALS.F34A.lookup "tag").map (fromWALS34A ·.value) = some tagalog.occurrence := by
  native_decide

theorem russian_ch34 :
    (Datasets.WALS.F34A.lookup "rus").map (fromWALS34A ·.value) = some russian.occurrence := by
  native_decide

theorem zulu_ch34 :
    (Datasets.WALS.F34A.lookup "zul").map (fromWALS34A ·.value) = some zulu.occurrence := by
  native_decide

theorem lezgian_ch34 :
    (Datasets.WALS.F34A.lookup "lez").map (fromWALS34A ·.value) = some lezgian.occurrence := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 35 (Plurality in Independent Personal Pronouns)
-- ============================================================================

-- Languages where WALS Ch 35 agrees with the hand-coded profile.
-- Several languages diverge between WALS and the profile's classification:
-- Japanese (WALS: personStemNominalPluralAffix, profile: personNumberStem),
-- Turkish (WALS: personStemNominalPluralAffix, profile: personNumberStem),
-- Finnish (WALS: personNumberStem, profile: pnStemPronominalAffix),
-- Hungarian (WALS: personNumberStem, profile: pnStemNominalAffix),
-- Korean (WALS: pnStemNominalAffix, profile: personNumberStem),
-- Hawaiian (WALS: pnStemPronominalAffix, profile: personNumberStem).

theorem english_ch35 :
    (Datasets.WALS.F35A.lookup "eng").map (fromWALS35A ·.value) = some english.pronounPlurality := by
  native_decide

theorem mandarin_ch35 :
    (Datasets.WALS.F35A.lookup "mnd").map (fromWALS35A ·.value) = some mandarin.pronounPlurality := by
  native_decide

theorem arabic_ch35 :
    (Datasets.WALS.F35A.lookup "aeg").map (fromWALS35A ·.value) = some arabic.pronounPlurality := by
  native_decide

theorem swahili_ch35 :
    (Datasets.WALS.F35A.lookup "swa").map (fromWALS35A ·.value) = some swahili.pronounPlurality := by
  native_decide

theorem indonesian_ch35 :
    (Datasets.WALS.F35A.lookup "ind").map (fromWALS35A ·.value) = some indonesian.pronounPlurality := by
  native_decide

theorem hindi_ch35 :
    (Datasets.WALS.F35A.lookup "hin").map (fromWALS35A ·.value) = some hindi.pronounPlurality := by
  native_decide

theorem tagalog_ch35 :
    (Datasets.WALS.F35A.lookup "tag").map (fromWALS35A ·.value) = some tagalog.pronounPlurality := by
  native_decide

theorem russian_ch35 :
    (Datasets.WALS.F35A.lookup "rus").map (fromWALS35A ·.value) = some russian.pronounPlurality := by
  native_decide

theorem zulu_ch35 :
    (Datasets.WALS.F35A.lookup "zul").map (fromWALS35A ·.value) = some zulu.pronounPlurality := by
  native_decide

theorem lezgian_ch35 :
    (Datasets.WALS.F35A.lookup "lez").map (fromWALS35A ·.value) = some lezgian.pronounPlurality := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 36 (The Associative Plural)
-- ============================================================================

-- Languages where WALS Ch 36 agrees with the hand-coded profile.
-- Several languages diverge: Mandarin (WALS: uniquePeriphrastic, profile:
-- sameAsAdditive), Japanese (WALS: sameAsAdditive, profile: uniquePeriphrastic),
-- Arabic (WALS: noAssociativePlural, profile: sameAsAdditive),
-- Swahili (WALS: uniquePeriphrastic, profile: absent),
-- Indonesian (WALS: uniquePeriphrastic, profile: absent),
-- Hindi (WALS: noAssociativePlural, profile: sameAsAdditive),
-- Hawaiian (WALS: uniquePeriphrastic, profile: absent).

theorem english_ch36 :
    (Datasets.WALS.F36A.lookup "eng").map (fromWALS36A ·.value) = some english.associativePlural := by
  native_decide

theorem turkish_ch36 :
    (Datasets.WALS.F36A.lookup "tur").map (fromWALS36A ·.value) = some turkish.associativePlural := by
  native_decide

theorem finnish_ch36 :
    (Datasets.WALS.F36A.lookup "fin").map (fromWALS36A ·.value) = some finnish.associativePlural := by
  native_decide

theorem hungarian_ch36 :
    (Datasets.WALS.F36A.lookup "hun").map (fromWALS36A ·.value) = some hungarian.associativePlural := by
  native_decide

theorem korean_ch36 :
    (Datasets.WALS.F36A.lookup "kor").map (fromWALS36A ·.value) = some korean.associativePlural := by
  native_decide

theorem tagalog_ch36 :
    (Datasets.WALS.F36A.lookup "tag").map (fromWALS36A ·.value) = some tagalog.associativePlural := by
  native_decide

theorem russian_ch36 :
    (Datasets.WALS.F36A.lookup "rus").map (fromWALS36A ·.value) = some russian.associativePlural := by
  native_decide

theorem zulu_ch36 :
    (Datasets.WALS.F36A.lookup "zul").map (fromWALS36A ·.value) = some zulu.associativePlural := by
  native_decide

theorem lezgian_ch36 :
    (Datasets.WALS.F36A.lookup "lez").map (fromWALS36A ·.value) = some lezgian.associativePlural := by
  native_decide

-- ============================================================================
-- WALS-Generated Distribution Counts
-- ============================================================================

/-- Ch 33 distribution derived from generated WALS data (1066 languages). -/
theorem ch33_suffix_count :
    (ch33.filter (·.value == .pluralSuffix)).length = 513 := by native_decide

theorem ch33_prefix_count :
    (ch33.filter (·.value == .pluralPrefix)).length = 126 := by native_decide

theorem ch33_pluralWord_count :
    (ch33.filter (·.value == .pluralWord)).length = 170 := by native_decide

theorem ch33_noPlural_count :
    (ch33.filter (·.value == .noPlural)).length = 98 := by native_decide

theorem ch33_mixedMorphological_count :
    (ch33.filter (·.value == .mixedMorphologicalPlural)).length = 60 := by native_decide

theorem ch33_pluralClitic_count :
    (ch33.filter (·.value == .pluralClitic)).length = 81 := by native_decide

/-- Ch 34 distribution derived from generated WALS data (291 languages). -/
theorem ch34_allNounsAlwaysObligatory_count :
    (ch34.filter (·.value == .allNounsAlwaysObligatory)).length = 133 := by native_decide

theorem ch34_allNounsAlwaysOptional_count :
    (ch34.filter (·.value == .allNounsAlwaysOptional)).length = 55 := by native_decide

theorem ch34_noNominalPlural_count :
    (ch34.filter (·.value == .noNominalPlural)).length = 28 := by native_decide

/-- Ch 35 distribution derived from generated WALS data (261 languages). -/
theorem ch35_personNumberStem_count :
    (ch35.filter (·.value == .personNumberStem)).length = 114 := by native_decide

/-- Ch 36 distribution derived from generated WALS data (236 languages). -/
theorem ch36_sameAsAdditive_count :
    (ch36.filter (·.value == .associativeSameAsAdditivePlural)).length = 104 := by native_decide

theorem ch36_noAssociativePlural_count :
    (ch36.filter (·.value == .noAssociativePlural)).length = 37 := by native_decide

/-- Suffixing is the single largest category in the full WALS 33A data
    (513/1066, ~48%), exceeding every other individual strategy. -/
theorem ch33_wals_suffixing_largest :
    (ch33.filter (·.value == .pluralSuffix)).length >
    (ch33.filter (·.value == .pluralPrefix)).length ∧
    (ch33.filter (·.value == .pluralSuffix)).length >
    (ch33.filter (·.value == .pluralWord)).length ∧
    (ch33.filter (·.value == .pluralSuffix)).length >
    (ch33.filter (·.value == .noPlural)).length := by native_decide

end Phenomena.Plurals.Typology
