import Linglib.Core.Word

/-!
# Cross-Linguistic Typology of Nominal Plurality (WALS Chapters 33--36)

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

## References

- Dryer, M. S. (2013). Coding of Nominal Plurality. In Dryer & Haspelmath (eds.),
  WALS Online (v2020.3). https://wals.info/chapter/33
- Haspelmath, M. (2013). Occurrence of Nominal Plurality. In Dryer & Haspelmath
  (eds.), WALS Online (v2020.3). https://wals.info/chapter/34
- Daniel, M. (2013). Plurality in Independent Personal Pronouns. In Dryer &
  Haspelmath (eds.), WALS Online (v2020.3). https://wals.info/chapter/35
- Daniel, M. & Moravcsik, E. (2013). The Associative Plural. In Dryer &
  Haspelmath (eds.), WALS Online (v2020.3). https://wals.info/chapter/36
- Corbett, G. G. (2000). Number. Cambridge University Press.
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
  deriving DecidableEq, BEq, Repr

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

/-- Actual WALS Ch 33 counts (Dryer 2013). -/
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
  deriving DecidableEq, BEq, Repr

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

/-- Actual WALS Ch 34 counts (Haspelmath 2013). -/
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
  deriving DecidableEq, BEq, Repr

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

/-- Actual WALS Ch 35 counts (Daniel 2013). -/
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
  deriving DecidableEq, BEq, Repr

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

/-- Actual WALS Ch 36 counts (Daniel & Moravcsik 2013). -/
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
  deriving Repr, BEq, DecidableEq

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

    This instantiates the hierarchy: pronouns > nouns for number marking
    (Smith-Stark 1974, Corbett 2000). -/
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

-- ============================================================================
-- The Animacy Hierarchy for Plural Marking
-- ============================================================================

/-- The animacy hierarchy for nominal plural marking (Smith-Stark 1974,
    Corbett 2000, Haspelmath WALS Ch 34). Languages mark plural on nouns
    according to an implicational scale:

      speaker > addressee > 3rd person > kin > human > higher animals >
      lower animals > discrete inanimates > nondiscrete inanimates

    If a language marks plural at a given point on the scale, it marks
    plural at all higher points. The WALS data captures the coarsest
    cut: human nouns vs inanimate nouns. -/
inductive AnimacyRank where
  | speaker
  | addressee
  | thirdPerson
  | kin
  | human
  | higherAnimal
  | lowerAnimal
  | discreteInanimate
  | nondiscreteInanimate
  deriving DecidableEq, BEq, Repr

/-- Numeric rank for comparison (higher = more likely to be plural-marked). -/
def AnimacyRank.toNat : AnimacyRank -> Nat
  | .speaker => 8
  | .addressee => 7
  | .thirdPerson => 6
  | .kin => 5
  | .human => 4
  | .higherAnimal => 3
  | .lowerAnimal => 2
  | .discreteInanimate => 1
  | .nondiscreteInanimate => 0

/-- The hierarchy predicts: if a language marks plural at rank r, it marks
    plural at all ranks above r. -/
def respectsHierarchy (markedRanks : List AnimacyRank) : Bool :=
  markedRanks.all fun r =>
    markedRanks.all fun r' =>
      -- If r' is ranked higher than r and r is marked, r' should also be marked
      r'.toNat >= r.toNat || markedRanks.contains r' == false

/-- The hierarchy is consistent: speaker outranks addressee outranks
    third person, and so forth down the scale. -/
theorem hierarchy_ordering :
    AnimacyRank.speaker.toNat > AnimacyRank.addressee.toNat ∧
    AnimacyRank.addressee.toNat > AnimacyRank.thirdPerson.toNat ∧
    AnimacyRank.thirdPerson.toNat > AnimacyRank.kin.toNat ∧
    AnimacyRank.kin.toNat > AnimacyRank.human.toNat ∧
    AnimacyRank.human.toNat > AnimacyRank.higherAnimal.toNat ∧
    AnimacyRank.higherAnimal.toNat > AnimacyRank.lowerAnimal.toNat ∧
    AnimacyRank.lowerAnimal.toNat > AnimacyRank.discreteInanimate.toNat ∧
    AnimacyRank.discreteInanimate.toNat > AnimacyRank.nondiscreteInanimate.toNat := by
  native_decide

end Phenomena.Plurals.Typology
