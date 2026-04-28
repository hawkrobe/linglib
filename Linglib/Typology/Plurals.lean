/-!
# Plural-marking typology — substrate types
@cite{wals-2013} (Chs 33-36)

Type-level enums + per-language profile struct for nominal and pronominal
plurality across @cite{wals-2013} chapters 33–36.

## Schema

- `PluralCoding` (Ch 33): how plurality is morphologically realized
- `PluralOccurrence` (Ch 34): when plural marking occurs (animacy + obligatoriness)
- `PronounPlurality` (Ch 35): how independent pronouns encode number
- `AssociativePlural` (Ch 36): "X and associates" construction
- `PluralityProfile`: per-language bundle of the four
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

end Typology
