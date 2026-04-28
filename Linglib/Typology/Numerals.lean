import Linglib.Typology.ClassifierSystem
import Linglib.Datasets.WALS.Features.F53A
import Linglib.Datasets.WALS.Features.F54A
import Linglib.Datasets.WALS.Features.F131A

/-!
# Numeral typology — substrate types and WALS data
@cite{wals-2013} (Chs 53, 54, 55, 56, 131) @cite{aikhenvald-2000}
@cite{greenberg-1978} @cite{stolz-veselinova-2013}

Type-level enums + per-language profile struct for numeral systems
across @cite{wals-2013} chapters 53–56 (Gil, Comrie) and 131:
ordinal formation, distributive numerals, numeral classifiers,
conjunction-quantifier identity, numeral base. Plus WALS distribution
data, the principal cross-linguistic generalizations, and the Greenberg
suppletion hierarchy for ordinal formation.

`ClassifierStatus` (WALS Ch 55) and `fromWALS55A` live in
`Typology/ClassifierSystem.lean` and are re-imported here.

## Schema

- `OrdinalFormation` (Ch 53): ordinal numeral formation
- `DistributiveNumeral` (Ch 54): distributive marking strategy
- `ConjunctionQuantifier` (Ch 56): identity of 'and' and 'all'
- `Region`: areal grouping (for cross-linguistic generalizations)
- `PluralMarking`: nominal plural status (Sanches-Slobin)
- `NumeralBase` (Ch 131): decimal/vigesimal/etc.
- `NumeralProfile`: per-language bundle

Per-language data lives in `Fragments/{Lang}/Numerals.lean`.
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

-- ============================================================================
-- WALS converters
-- ============================================================================

/-- Convert WALS 53A ordinal numeral values to the substrate enum.
    WALS distinguishes eight subtypes; we collapse them into five categories.
    "First, two-th, three-th" and "First, two, three" both map to
    `firstSuppletion` (only "first" suppletive). "One, two, three" and
    "First/one-th, …" map to `various`. -/
def fromWALS53A : Datasets.WALS.F53A.OrdinalNumerals → OrdinalFormation
  | .none => .noOrdinals
  | .oneTwoThree => .various
  | .firstTwoThree => .firstSuppletion
  | .oneThTwoThThreeTh => .allFromCardinals
  | .firstOneThTwoThThreeTh => .various
  | .firstTwoThThreeTh => .firstSuppletion
  | .firstSecondThreeTh => .firstSecondSuppletion
  | .various => .various

/-- Convert WALS 54A distributive numeral values to the substrate enum.
    Word-level and mixed strategies collapse into `markedByOtherMeans`. -/
def fromWALS54A : Datasets.WALS.F54A.DistributiveNumerals → DistributiveNumeral
  | .noDistributiveNumerals => .noDistributive
  | .markedByReduplication => .markedByReduplication
  | .markedByPrefix => .markedByPrefix
  | .markedBySuffix => .markedBySuffix
  | .markedByPrecedingWord => .markedByOtherMeans
  | .markedByFollowingWord => .markedByOtherMeans
  | .markedByMixedOrOtherStrategies => .markedByOtherMeans

/-- Convert WALS 131A numeral base values to the substrate enum (one-to-one). -/
def fromWALS131A : Datasets.WALS.F131A.NumeralBases → NumeralBase
  | .decimal => .decimal
  | .pureVigesimal => .vigesimal
  | .hybridVigesimalDecimal => .hybridVigesimalDecimal
  | .otherBase => .otherBase
  | .extendedBodyPartSystem => .bodyPartSystem
  | .restricted => .restricted

-- ============================================================================
-- WALS distribution data (Ch 53, 54, 56)
-- ============================================================================

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

/-- WALS Ch 53 counts (321 languages). -/
def ch53Distribution : OrdinalDistribution :=
  { firstSuppletion := 99
  , firstSecondSuppletion := 45
  , allFromCardinals := 28
  , various := 83
  , noOrdinals := 66 }

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

/-- WALS Ch 54 counts (251 languages). -/
def ch54Distribution : DistributiveDistribution :=
  { noDistributive := 63
  , reduplication := 85
  , suffixCount := 34
  , prefixCount := 19
  , otherMeans := 50 }

/-- WALS Chapter 56 distribution: language counts per conjunction-quantifier
    type. Total: 220 languages. -/
structure ConjQuantDistribution where
  identity : Nat
  differentiation : Nat
  deriving Repr

def ConjQuantDistribution.total (d : ConjQuantDistribution) : Nat :=
  d.identity + d.differentiation

/-- WALS Ch 56 counts (220 languages). -/
def ch56Distribution : ConjQuantDistribution :=
  { identity := 43
  , differentiation := 177 }

-- ============================================================================
-- Cross-linguistic generalizations: ordinals (Ch 53)
-- ============================================================================

/-- Suppletive "first" is the dominant ordinal formation strategy (WALS Ch 53).
    Languages with suppletive "first" (alone or with suppletive "second")
    outnumber languages where all ordinals derive regularly from cardinals. -/
theorem suppletive_first_dominant :
    ch53Distribution.firstSuppletion + ch53Distribution.firstSecondSuppletion >
    ch53Distribution.allFromCardinals := by decide

/-- "First" suppletion alone is the single most common ordinal pattern. -/
theorem first_suppletion_most_common :
    ch53Distribution.firstSuppletion > ch53Distribution.firstSecondSuppletion ∧
    ch53Distribution.firstSuppletion > ch53Distribution.allFromCardinals ∧
    ch53Distribution.firstSuppletion > ch53Distribution.noOrdinals := by decide

/-- Languages with some form of ordinal formation (regular or suppletive)
    outnumber languages lacking ordinals entirely. -/
theorem most_languages_have_ordinals :
    ch53Distribution.firstSuppletion + ch53Distribution.firstSecondSuppletion +
    ch53Distribution.allFromCardinals + ch53Distribution.various >
    ch53Distribution.noOrdinals * 3 := by decide

-- ============================================================================
-- Cross-linguistic generalizations: distributives (Ch 54)
-- ============================================================================

/-- Languages with dedicated distributive numeral forms outnumber those
    without, but neither is a negligible minority. -/
theorem distributive_majority_has_marking :
    ch54Distribution.reduplication + ch54Distribution.suffixCount +
    ch54Distribution.prefixCount + ch54Distribution.otherMeans >
    ch54Distribution.noDistributive := by decide

/-- Reduplication is the single most common distributive strategy,
    outnumbering any other individual morphological means. -/
theorem reduplication_most_common_distributive :
    ch54Distribution.reduplication > ch54Distribution.suffixCount ∧
    ch54Distribution.reduplication > ch54Distribution.prefixCount ∧
    ch54Distribution.reduplication > ch54Distribution.otherMeans ∧
    ch54Distribution.reduplication > ch54Distribution.noDistributive := by decide

-- ============================================================================
-- Cross-linguistic generalizations: conjunctions and quantifiers (Ch 56)
-- ============================================================================

/-- Differentiation between 'and' and 'all' is the dominant pattern (WALS Ch 56). -/
theorem differentiation_dominant :
    ch56Distribution.differentiation > ch56Distribution.identity := by decide

/-- Differentiation accounts for more than three-quarters of the sample. -/
theorem differentiation_supermajority :
    ch56Distribution.differentiation * 4 > ch56Distribution.total * 3 := by decide

/-- Identity between 'and' and 'all' is a non-negligible minority pattern,
    attested in roughly a fifth of languages (43 out of 220). -/
theorem identity_nonnegligible :
    ch56Distribution.identity * 6 ≥ ch56Distribution.total := by decide

-- ============================================================================
-- Greenberg's suppletion hierarchy for ordinals
-- ============================================================================

/-- @cite{greenberg-1978}'s implicational universal for ordinal suppletion:
    if a language has a suppletive ordinal for numeral N, then it has
    suppletive ordinals for all numerals less than N. Equivalently:
    suppletion cuts off at some point in the sequence 1st, 2nd, 3rd,…
    and all ordinals above the cutoff are regular.

    The WALS data captures the coarsest version: suppletion is most likely
    for "first", less likely for "second", and rare beyond that. -/
inductive SuppletionCutoff where
  /-- No suppletive ordinals (all regular from cardinals). -/
  | none
  /-- Only "first" is suppletive. -/
  | first
  /-- "first" and "second" are suppletive. -/
  | firstAndSecond
  deriving DecidableEq, Repr

/-- Numeric rank for the suppletion cutoff (higher = more suppletion). -/
def SuppletionCutoff.rank : SuppletionCutoff → Nat
  | .none => 0
  | .first => 1
  | .firstAndSecond => 2

/-- Map ordinal formation type to suppletion cutoff. Languages with 'various'
    or 'no ordinals' patterns are excluded from the hierarchy. -/
def OrdinalFormation.suppletionCutoff : OrdinalFormation → Option SuppletionCutoff
  | .allFromCardinals => some .none
  | .firstSuppletion => some .first
  | .firstSecondSuppletion => some .firstAndSecond
  | .various => Option.none
  | .noOrdinals => Option.none

/-- The hierarchy is consistent: rank of each cutoff increases monotonically. -/
theorem suppletion_hierarchy_ordering :
    SuppletionCutoff.none.rank < SuppletionCutoff.first.rank ∧
    SuppletionCutoff.first.rank < SuppletionCutoff.firstAndSecond.rank := by decide

/-- WALS aggregate confirms the hierarchy: languages with "first"-only
    suppletion outnumber those with "first+second" suppletion, which in turn
    outnumber those with no suppletion at all. This reflects the implicational
    scale: suppletion at higher numerals is rarer. -/
theorem suppletion_frequency_matches_hierarchy :
    ch53Distribution.firstSuppletion > ch53Distribution.firstSecondSuppletion ∧
    ch53Distribution.firstSecondSuppletion > ch53Distribution.allFromCardinals := by
  decide

end Typology
