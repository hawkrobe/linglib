import Linglib.Typology.ClassifierSystem

/-!
# Numeral typology — substrate types
@cite{wals-2013} (Chs 53, 54, 55, 56, 131)

Type-level enums + per-language profile struct for numeral systems
across @cite{wals-2013} chapters 53–56 (Gil, Comrie) and 131:
ordinal formation, distributive numerals, numeral classifiers,
conjunction-quantifier identity, numeral base.

`ClassifierStatus` (WALS Ch 55) lives in `Typology/ClassifierSystem.lean`
and is re-imported here for `NumeralProfile.classifier`.

## Schema

- `OrdinalFormation` (Ch 53): ordinal numeral formation
- `DistributiveNumeral` (Ch 54): distributive marking strategy
- `ConjunctionQuantifier` (Ch 56): identity of 'and' and 'all'
- `Region`: areal grouping (for cross-linguistic generalizations)
- `PluralMarking`: nominal plural status (Sanches-Slobin)
- `NumeralBase` (Ch 131): decimal/vigesimal/etc.
- `NumeralProfile`: per-language bundle
-/

set_option autoImplicit false

namespace Typology

/-- WALS Ch 53: how a language forms ordinal numerals from cardinals.
    The dominant pattern is "first" suppletive + higher ordinals regular. -/
inductive OrdinalFormation where
  /-- "first" is suppletive, "second" onward regular (e.g., English). -/
  | firstSuppletion
  /-- "first" and "second" suppletive, "third" onward regular. -/
  | firstSecondSuppletion
  /-- All ordinals derived regularly from cardinals. -/
  | allFromCardinals
  /-- Mixed strategies, no single dominant pattern. -/
  | various
  /-- No productive ordinal formation reported. -/
  | noOrdinals
  deriving DecidableEq, Repr

/-- WALS Ch 54: whether and how a language marks distributive numerals
    ("N each" / "N apiece"). Reduplication is the most widespread
    dedicated strategy. -/
inductive DistributiveNumeral where
  /-- No dedicated distributive numeral form. -/
  | noDistributive
  /-- Cardinal is reduplicated (e.g., Turkish iki-şer, Tagalog dalawa-dalawa). -/
  | markedByReduplication
  /-- Suffix creates distributive (e.g., Georgian -agan). -/
  | markedBySuffix
  /-- Prefix creates distributive. -/
  | markedByPrefix
  /-- Other strategies (particles, circumfix, etc.). -/
  | markedByOtherMeans
  deriving DecidableEq, Repr

/-- WALS Ch 56 (Gil): relationship between 'and' and 'all/every'.
    Identity reflects a deep connection between conjunction (exhaustive
    pairing) and universal quantification (exhaustive predication). -/
inductive ConjunctionQuantifier where
  /-- Same morpheme for 'and' and 'all' (e.g., Mandarin dou, Tagalog lahat). -/
  | identity
  /-- Different morphemes (e.g., English and/all, Japanese to/subete). -/
  | differentiation
  deriving DecidableEq, Repr

/-- Areal region — used for areal generalizations about classifier
    distribution (e.g., Sanches-Slobin's classifier-belt observation). -/
inductive Region where
  | europe | eastAsia | southeastAsia | southAsia | centralAsia
  | westAsia | africa | northAmerica | mesoamerica | southAmerica | oceania
  deriving DecidableEq, Repr

/-- Whether a language has obligatory grammatical plural marking on
    common nouns. Used for the Sanches-Slobin generalization
    relating numeral classifiers and plural. -/
inductive PluralMarking where
  /-- Plural marking required (e.g., English, Spanish). -/
  | obligatory
  /-- Plural marking available but not required (e.g., Korean). -/
  | optional
  /-- No grammatical plural on nouns (e.g., Mandarin, Japanese). -/
  | none
  deriving DecidableEq, Repr

/-- WALS Ch 131 (Comrie): the base of a language's numeral system.
    Most languages use a decimal (base-10) system. -/
inductive NumeralBase where
  /-- Base 10 (e.g., English, Mandarin, Swahili). -/
  | decimal
  /-- Pure base 20 (e.g., Ainu, Chukchi). -/
  | vigesimal
  /-- Mixed base-20 / base-10 (e.g., French, Basque, Georgian). -/
  | hybridVigesimalDecimal
  /-- Base 5, 6, or other (rare). -/
  | otherBase
  /-- Extended body-part counting system (e.g., Eipo). -/
  | bodyPartSystem
  /-- Restricted numeral system (few numerals, no productive base). -/
  | restricted
  deriving DecidableEq, Repr

/-- A language's numeral typology profile across all four WALS dimensions
    + areal region + plural-marking status. -/
structure NumeralProfile where
  language : String
  /-- ISO 639-3 code. -/
  iso : String
  /-- Ch 53: ordinal numeral formation. -/
  ordinal : OrdinalFormation
  /-- Ch 54: distributive numeral marking. -/
  distributive : DistributiveNumeral
  /-- Ch 55: numeral classifier status. -/
  classifier : ClassifierStatus
  /-- Ch 56: conjunction-quantifier relationship. -/
  conjQuant : ConjunctionQuantifier
  /-- Areal region (for areal generalizations). -/
  region : Region
  /-- Plural marking on common nouns (for Sanches-Slobin). -/
  pluralMarking : PluralMarking
  /-- Ch 131: numeral base (optional; not all languages surveyed). -/
  numeralBase : Option NumeralBase := Option.none
  deriving Repr, DecidableEq

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

end Typology
