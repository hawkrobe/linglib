import Linglib.Datasets.WALS.Features.F33A
import Linglib.Datasets.WALS.Features.F34A
import Linglib.Datasets.WALS.Features.F35A
import Linglib.Datasets.WALS.Features.F36A

/-!
# Plural-marking typology — substrate types and WALS data
@cite{wals-2013} (Chs 33-36) @cite{corbett-2000}

Type-level enums + per-language profile struct for nominal and pronominal
plurality across @cite{wals-2013} chapters 33–36, plus WALS distribution
data and the principal cross-linguistic generalizations.

## Schema

- `PluralCoding` (Ch 33): how plurality is morphologically realized
- `PluralOccurrence` (Ch 34): when plural marking occurs (animacy + obligatoriness)
- `PronounPlurality` (Ch 35): how independent pronouns encode number
- `AssociativePlural` (Ch 36): "X and associates" construction
- `PluralityProfile`: per-language bundle of the four

Per-language data lives in `Fragments/{Lang}/Plurals.lean`.

## Layer discipline

This file is substrate: enums, profile struct, predicates, WALS converters,
WALS distribution data, cross-linguistic generalizations stated against the
distribution data. No Fragment imports.
-/

set_option autoImplicit false

namespace Typology

/-- WALS Ch 33: how plurality is morphologically coded on full nouns.
    Nine values cross morphological strategy with absence-of-marking. -/
inductive PluralCoding where
  /-- Plural prefix (e.g., Swahili wa-toto 'children'). -/
  | prefix
  /-- Plural suffix (e.g., English dog-s). -/
  | suffix
  /-- Stem-internal vowel change (e.g., Maricopa humar/humaar). -/
  | stemChange
  /-- Tonal change (e.g., Ngiti kamà/kámá 'chief/chiefs'). -/
  | tone
  /-- Complete reduplication (e.g., Indonesian rumah-rumah). -/
  | reduplication
  /-- Two or more methods, none primary (e.g., Arabic). -/
  | mixedMorphological
  /-- Separate word in NP (e.g., Hawaiian mau, Mandarin 些). -/
  | pluralWord
  /-- NP-level clitic (e.g., Cayuvava me=). -/
  | pluralClitic
  /-- No indication of plurality. -/
  | noPlural
  deriving DecidableEq, Repr

/-- WALS Ch 34: when plural marking occurs on full nouns. Cross of
    animacy scope (none / human-only / all) and obligatoriness
    (optional / obligatory). -/
inductive PluralOccurrence where
  /-- No nominal plural at all. -/
  | noNominalPlural
  /-- Plural only on human nouns, optional. -/
  | humanOnlyOptional
  /-- Plural only on human nouns, obligatory. -/
  | humanOnlyObligatory
  /-- Plural on all nouns, always optional. -/
  | allNounsAlwaysOptional
  /-- Plural on all nouns, obligatory for human, optional for inanimate. -/
  | allNounsOptionalInanimates
  /-- Plural on all nouns, always obligatory. -/
  | allNounsAlwaysObligatory
  deriving DecidableEq, Repr

/-- WALS Ch 35: how independent personal pronouns encode number. -/
inductive PronounPlurality where
  /-- No independent subject pronouns (e.g., Acoma). -/
  | noIndependentPronouns
  /-- Same form for sg and pl (e.g., Pirahã ti 'I/we'). -/
  | numberIndifferent
  /-- Both person and number are affixal. -/
  | personNumberAffixes
  /-- Person+number fused in stem (e.g., Dogon mi/emme). -/
  | personNumberStem
  /-- Person-number stem + pronominal plural affix. -/
  | pnStemPronominalAffix
  /-- Person-number stem + nominal plural affix (e.g., Russian). -/
  | pnStemNominalAffix
  /-- Person stem + pronominal plural affix (e.g., Chuvash). -/
  | personStemPronominalAffix
  /-- Person stem + nominal plural affix (e.g., Mandarin -men). -/
  | personStemNominalAffix
  deriving DecidableEq, Repr

/-- WALS Ch 36: associative plural marking ("X and associates").
    The typological split is between marker-overlap with additive
    plural vs dedicated associative form. -/
inductive AssociativePlural where
  /-- Marker also used for additive plural (e.g., Zulu, Turkish). -/
  | sameAsAdditive
  /-- Dedicated affix (e.g., Hungarian -ek). -/
  | uniqueAffixal
  /-- Dedicated free/clitic marker (e.g., Tagalog, Japanese -tachi). -/
  | uniquePeriphrastic
  /-- No productive associative plural (e.g., Russian, English). -/
  | absent
  deriving DecidableEq, Repr

/-- A language's plurality profile across @cite{wals-2013} Chs 33-36. -/
structure PluralityProfile where
  /-- Language name (matches `LanguageProfile.name` when bundled). -/
  language : String
  /-- ISO 639-3 code (matches `LanguageProfile.iso` when bundled). -/
  iso : String
  /-- Ch 33: how plurality is coded on nouns. -/
  coding : PluralCoding
  /-- Ch 34: when plural marking occurs. -/
  occurrence : PluralOccurrence
  /-- Ch 35: pronoun plurality type. -/
  pronounPlurality : PronounPlurality
  /-- Ch 36: associative plural strategy. -/
  associativePlural : AssociativePlural
  deriving Repr, DecidableEq

/-- Does a language have morphological plural marking on nouns? -/
def PluralityProfile.hasMorphologicalPlural (p : PluralityProfile) : Bool :=
  p.coding != .noPlural && p.coding != .pluralWord && p.coding != .pluralClitic

/-- Does a language have obligatory plural marking on all nouns? -/
def PluralityProfile.hasObligatoryPlural (p : PluralityProfile) : Bool :=
  p.occurrence == .allNounsAlwaysObligatory ||
  p.occurrence == .allNounsOptionalInanimates

/-- Does a language distinguish number in independent pronouns? -/
def PluralityProfile.pronounsDistinguishNumber (p : PluralityProfile) : Bool :=
  p.pronounPlurality != .noIndependentPronouns &&
  p.pronounPlurality != .numberIndifferent

-- ============================================================================
-- WALS converters
-- ============================================================================

/-- Convert a WALS 33A coding value into the substrate enum. -/
def fromWALS33A : Datasets.WALS.F33A.PluralityCoding → PluralCoding
  | .pluralPrefix => .prefix
  | .pluralSuffix => .suffix
  | .pluralStemChange => .stemChange
  | .pluralTone => .tone
  | .pluralCompleteReduplication => .reduplication
  | .mixedMorphologicalPlural => .mixedMorphological
  | .pluralWord => .pluralWord
  | .pluralClitic => .pluralClitic
  | .noPlural => .noPlural

/-- Convert a WALS 34A occurrence value into the substrate enum. -/
def fromWALS34A : Datasets.WALS.F34A.PluralityOccurrence → PluralOccurrence
  | .noNominalPlural => .noNominalPlural
  | .onlyHumanNounsOptional => .humanOnlyOptional
  | .onlyHumanNounsObligatory => .humanOnlyObligatory
  | .allNounsAlwaysOptional => .allNounsAlwaysOptional
  | .allNounsOptionalInInanimates => .allNounsOptionalInanimates
  | .allNounsAlwaysObligatory => .allNounsAlwaysObligatory

/-- Convert a WALS 35A pronoun-plurality value into the substrate enum. -/
def fromWALS35A : Datasets.WALS.F35A.PronounPlurality → PronounPlurality
  | .noIndependentSubjectPronouns => .noIndependentPronouns
  | .numberIndifferentPronouns => .numberIndifferent
  | .personNumberAffixes => .personNumberAffixes
  | .personNumberStem => .personNumberStem
  | .personNumberStemPronominalPluralAffix => .pnStemPronominalAffix
  | .personNumberStemNominalPluralAffix => .pnStemNominalAffix
  | .personStemPronominalPluralAffix => .personStemPronominalAffix
  | .personStemNominalPluralAffix => .personStemNominalAffix

/-- Convert a WALS 36A associative-plural value into the substrate enum. -/
def fromWALS36A : Datasets.WALS.F36A.AssociativePlural → AssociativePlural
  | .associativeSameAsAdditivePlural => .sameAsAdditive
  | .uniqueAffixalAssociativePlural => .uniqueAffixal
  | .uniquePeriphrasticAssociativePlural => .uniquePeriphrastic
  | .noAssociativePlural => .absent

-- ============================================================================
-- WALS distribution data (Corbett 2000 reference counts; smaller subset
-- than the full generated WALS data files)
-- ============================================================================

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

/-- WALS Ch 33 counts (957 languages). -/
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

/-- WALS Ch 34 counts (290 languages). -/
def ch34Distribution : PluralOccurrenceDistribution :=
  { noNominalPlural := 28
  , humanOnlyOptional := 20
  , humanOnlyObligatory := 39
  , allNounsAlwaysOptional := 55
  , allNounsOptionalInanimates := 15
  , allNounsAlwaysObligatory := 133 }

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

/-- WALS Ch 35 counts (260 languages). -/
def ch35Distribution : PronounPluralityDistribution :=
  { noIndependentPronouns := 2
  , numberIndifferent := 8
  , personNumberAffixes := 25
  , personNumberStem := 114
  , pnStemPronominalAffix := 47
  , pnStemNominalAffix := 22
  , personStemPronominalAffix := 23
  , personStemNominalAffix := 19 }

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

/-- WALS Ch 36 counts (237 languages). -/
def ch36Distribution : AssociativePluralDistribution :=
  { sameAsAdditive := 104
  , uniqueAffixal := 48
  , uniquePeriphrastic := 48
  , absent := 37 }

-- ============================================================================
-- Cross-linguistic generalizations
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
    ch33Distribution.suffixCount > ch33Distribution.reduplication := by decide

/-- Over half of all sampled languages use plural suffixes. -/
theorem suffixing_is_majority :
    ch33Distribution.suffixCount * 2 > ch33Distribution.total := by decide

/-- Obligatory marking on all nouns is the most common occurrence pattern
    (WALS Ch 34): 133 out of 290 languages. -/
theorem obligatory_all_most_common :
    ch34Distribution.allNounsAlwaysObligatory > ch34Distribution.noNominalPlural ∧
    ch34Distribution.allNounsAlwaysObligatory > ch34Distribution.humanOnlyOptional ∧
    ch34Distribution.allNounsAlwaysObligatory > ch34Distribution.humanOnlyObligatory ∧
    ch34Distribution.allNounsAlwaysObligatory > ch34Distribution.allNounsAlwaysOptional ∧
    ch34Distribution.allNounsAlwaysObligatory > ch34Distribution.allNounsOptionalInanimates := by
  decide

/-- The animacy hierarchy for nominal plurality (Haspelmath, Ch 34):
    human nouns are more likely to have plural marking than inanimates.
    In the WALS sample, no language has plural only on inanimates ---
    the three logically possible "inanimate-only" types are unattested.
    This is captured here as: human-only plural counts (59) are positive. -/
theorem animacy_hierarchy_human_over_inanimate :
    ch34Distribution.humanOnlyOptional + ch34Distribution.humanOnlyObligatory > 0 := by
  decide

/-- Person-number stems dominate pronoun plurality (WALS Ch 35).
    114/260 languages fuse person and number into an unanalysable stem
    (e.g. English I/we, Dogon mi/emme). -/
theorem person_number_stem_dominant :
    ch35Distribution.personNumberStem > ch35Distribution.personNumberAffixes ∧
    ch35Distribution.personNumberStem > ch35Distribution.pnStemPronominalAffix ∧
    ch35Distribution.personNumberStem > ch35Distribution.pnStemNominalAffix ∧
    ch35Distribution.personNumberStem > ch35Distribution.personStemPronominalAffix ∧
    ch35Distribution.personNumberStem > ch35Distribution.personStemNominalAffix ∧
    ch35Distribution.personNumberStem > ch35Distribution.numberIndifferent ∧
    ch35Distribution.personNumberStem > ch35Distribution.noIndependentPronouns := by
  decide

/-- Nearly all languages distinguish number in pronouns: only 10/260
    languages lack number distinctions in independent personal pronouns
    (2 with no independent pronouns + 8 number-indifferent). -/
theorem pronoun_number_near_universal :
    ch35Distribution.noIndependentPronouns + ch35Distribution.numberIndifferent < 15 ∧
    ch35Distribution.total -
      (ch35Distribution.noIndependentPronouns + ch35Distribution.numberIndifferent) > 240 := by
  decide

/-- Associative plurals are widespread: 200/237 sampled languages have
    some form of associative plural (only 37 lack them entirely). -/
theorem associative_plural_widespread :
    ch36Distribution.sameAsAdditive + ch36Distribution.uniqueAffixal +
      ch36Distribution.uniquePeriphrastic > ch36Distribution.absent * 5 := by
  decide

/-- In nearly half of languages with associative plurals, the associative
    marker overlaps with the additive plural marker (104/200 languages
    with associative plurals). -/
theorem associative_often_overlaps_additive :
    ch36Distribution.sameAsAdditive * 2 ≥
      ch36Distribution.uniqueAffixal + ch36Distribution.uniquePeriphrastic := by
  decide

end Typology
