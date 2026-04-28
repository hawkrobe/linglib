import Linglib.Datasets.WALS.Features.F70A
import Linglib.Datasets.WALS.Features.F71A
import Linglib.Datasets.WALS.Features.F72A
import Linglib.Datasets.WALS.Features.F73A

/-!
# Imperative-system typology — substrate types and WALS data
@cite{wals-2013} (Chs 70, 71, 72, 73) @cite{van-der-auwera-lejeune-2013}

Type-level enums + per-language profile struct for the imperative-prohibitive-
hortative-jussive-optative complex across @cite{wals-2013} chapters 70–73,
plus WALS distribution data and the principal cross-linguistic generalizations
from van der Auwera & Lejeune (2013).

## Schema

- `MorphImpType` (Ch 70): morphological imperative status
- `ProhibitiveType` (Ch 71): prohibitive construction (verb form × negation type)
- `ImpHortSystem` (Ch 72): hortative/jussive paradigm richness
- `OptativePresence` (Ch 73): dedicated optative present/absent
- `ImperativeProfile`: per-language bundle

Per-language data lives in `Fragments/{Lang}/Directives.lean`.
-/

set_option autoImplicit false

namespace Typology

-- ============================================================================
-- WALS Ch 70: The morphological imperative
-- ============================================================================

/-- WALS Ch 70: whether a language has a dedicated morphological imperative,
    and if so whether the paradigm extends beyond 2nd person.
    @cite{van-der-auwera-lejeune-2013}: 426/548 (77.7%) of sampled languages
    have some morphological imperative; only 122 lack one entirely. -/
inductive MorphImpType where
  /-- Dedicated morphological imperative for second person only
      (e.g., English *Go!*, Turkish *Gel!*). -/
  | secondOnly
  /-- Morphological imperative for second person and other persons
      (1st-inclusive, 3rd jussive; e.g., Latin *i*/*eamus*, Quechua). -/
  | secondAndOther
  /-- No dedicated morphological imperative; commands use bare stems,
      indicative forms, particles, or intonation
      (e.g., Mandarin Chinese, many isolating languages). -/
  | noMorphological
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 71: The prohibitive
-- ============================================================================

/-- WALS Ch 71: how prohibitives ("Don't!") are formed. Cross-tabulation of
    two binary features: is the imperative construction the SAME as the
    affirmative or SPECIAL, and is the negation strategy SAME as in
    declaratives or SPECIAL? Yields four structural types.

    The key typological finding (@cite{van-der-auwera-lejeune-2013}): Type 1
    (normal+normal) is surprisingly uncommon — languages tend to treat
    prohibitives differently from simple negation of an imperative. -/
inductive ProhibitiveType where
  /-- Type 1: normal imperative + normal negation
      (e.g., Korean *kala* → *kaci malla*; Hungarian *menj!* → *ne menj!*). -/
  | normalImpNormalNeg
  /-- Type 2: normal imperative + special negation
      (e.g., Ancient Greek declarative *ou* vs imperative *mē*). -/
  | normalImpSpecialNeg
  /-- Type 3: special imperative + normal negation
      (e.g., Italian *va!* → *non andare!*, infinitive replaces imperative). -/
  | specialImpNormalNeg
  /-- Type 4: special imperative + special negation
      (e.g., Latin *ne eas!*; many Austronesian and African languages). -/
  | specialImpSpecialNeg
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 72: Imperative-hortative systems
-- ============================================================================

/-- WALS Ch 72: paradigm richness for non-2nd-person commands. Whether the
    language has morphological hortative (1st-person *let's*) and/or jussive
    (3rd-person *let him*) in addition to the basic 2nd-person imperative. -/
inductive ImpHortSystem where
  /-- Imperative only: morphological 2nd-person commands but no dedicated
      hortative or jussive (e.g., English uses periphrastic *let's*). -/
  | imperativeOnly
  /-- Imperative + hortative: morphological 2SG + 1PL forms
      (e.g., Turkish *gel!* / *gelelim*). -/
  | imperativeAndHortative
  /-- Imperative + jussive: morphological 2nd + 3rd person forms
      (e.g., Hindi-Urdu *jao* / *jaae*). -/
  | imperativeAndJussive
  /-- All three: dedicated 2nd, 1st, and 3rd-person command forms
      (e.g., Latin *i*/*eamus*/*eat*; Georgian; Quechua). -/
  | allThree
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 73: The optative
-- ============================================================================

/-- WALS Ch 73: whether the language has a morphologically dedicated optative
    (mood expressing wishes: *may it rain*, *if only she were here*).
    Languages that express wishes only via particles, intonation, or
    subjunctive forms shared with other functions are classified as lacking
    a dedicated optative. -/
inductive OptativePresence where
  /-- Morphologically dedicated optative present
      (e.g., Ancient Greek *-oimi*, Turkish *-sA*, Georgian). -/
  | present
  /-- No dedicated morphological optative; wishes via subjunctive, particles,
      conditional, or periphrasis (e.g., English, Mandarin, Japanese). -/
  | absent
  deriving DecidableEq, Repr

-- ============================================================================
-- Per-language profile
-- ============================================================================

/-- A language's imperative-system profile across @cite{wals-2013} Chs 70–73. -/
structure ImperativeProfile where
  language : String
  iso : String := ""
  /-- Ch 70: morphological imperative type. -/
  morphImp : MorphImpType
  /-- Ch 71: prohibitive construction type. -/
  prohibitive : ProhibitiveType
  /-- Ch 72: imperative-hortative system. -/
  impHortSystem : ImpHortSystem
  /-- Ch 73: optative presence (none if language not in Ch 73 sample). -/
  optative : Option OptativePresence := none
  /-- Illustrative imperative form(s) for documentation. -/
  impForms : List String := []
  /-- Notes on the imperative system. -/
  notes : String := ""
  deriving Repr

/-- Does a language have a morphological imperative (of any type)? -/
def ImperativeProfile.hasMorphImp (p : ImperativeProfile) : Bool :=
  p.morphImp != .noMorphological

/-- Does a language have an extended imperative paradigm (beyond 2nd person)? -/
def ImperativeProfile.hasExtendedParadigm (p : ImperativeProfile) : Bool :=
  p.morphImp == .secondAndOther

/-- Does a language have a hortative? -/
def ImperativeProfile.hasHortative (p : ImperativeProfile) : Bool :=
  p.impHortSystem == .imperativeAndHortative ||
  p.impHortSystem == .allThree

/-- Does a language have a jussive? -/
def ImperativeProfile.hasJussive (p : ImperativeProfile) : Bool :=
  p.impHortSystem == .imperativeAndJussive ||
  p.impHortSystem == .allThree

/-- Does a language have a dedicated optative? -/
def ImperativeProfile.hasOptative (p : ImperativeProfile) : Bool :=
  p.optative == some .present

/-- Does a language use a special prohibitive construction (Type 2/3/4) —
    i.e., does the prohibitive differ from simply negating the imperative? -/
def ImperativeProfile.hasSpecialProhibitive (p : ImperativeProfile) : Bool :=
  p.prohibitive != .normalImpNormalNeg

-- ============================================================================
-- WALS converters
-- ============================================================================

/-- Convert WALS 70A (number distinctions in 2nd-person imperative) into the
    substrate enum. F70A tracks number distinctions, not whether the paradigm
    extends to other persons, so only `noSecondPersonImperatives` produces a
    determinate `noMorphological` value; other values return `none`. -/
def fromWALS70A : Datasets.WALS.F70A.MorphologicalImperative → Option MorphImpType
  | .noSecondPersonImperatives => some .noMorphological
  | _ => none

/-- Convert WALS 71A prohibitive values into the substrate enum (one-to-one). -/
def fromWALS71A : Datasets.WALS.F71A.Prohibitive → ProhibitiveType
  | .normalImperativeNormalNegative => .normalImpNormalNeg
  | .normalImperativeSpecialNegative => .normalImpSpecialNeg
  | .specialImperativeNormalNegative => .specialImpNormalNeg
  | .specialImperativeSpecialNegative => .specialImpSpecialNeg

/-- Convert WALS 72A imperative-hortative system values into the substrate enum.
    WALS uses `maximalSystem` / `minimalSystem` / `bothTypesOfSystem` /
    `neitherTypeOfSystem`; only the two extreme values map cleanly to the
    substrate's four-way split. -/
def fromWALS72A : Datasets.WALS.F72A.ImperativeHortativeSystems → Option ImpHortSystem
  | .neitherTypeOfSystem => some .imperativeOnly
  | .maximalSystem => some .allThree
  | _ => none

/-- Convert WALS 73A optative values into the substrate enum (one-to-one). -/
def fromWALS73A : Datasets.WALS.F73A.Optative → OptativePresence
  | .present => .present
  | .absent => .absent

-- ============================================================================
-- WALS distribution data
-- ============================================================================

/-- WALS Ch 70 distribution: morphological imperative number distinctions
    (n = 548). -/
structure MorphImpCounts where
  secondSingularAndSecondPlural : Nat
  secondSingular : Nat
  secondPlural : Nat
  secondPersonNumberNeutral : Nat
  noSecondPersonImperatives : Nat
  deriving Repr

def MorphImpCounts.total (c : MorphImpCounts) : Nat :=
  c.secondSingularAndSecondPlural + c.secondSingular + c.secondPlural +
  c.secondPersonNumberNeutral + c.noSecondPersonImperatives

/-- Total languages in the Ch 70 sample with some morphological imperative. -/
def MorphImpCounts.withMorphImp (c : MorphImpCounts) : Nat :=
  c.secondSingularAndSecondPlural + c.secondSingular + c.secondPlural +
  c.secondPersonNumberNeutral

/-- WALS Ch 70 counts (548 languages, @cite{van-der-auwera-lejeune-2013}). -/
def ch70Distribution : MorphImpCounts :=
  { secondSingularAndSecondPlural := 292
  , secondSingular := 78
  , secondPlural := 38
  , secondPersonNumberNeutral := 18
  , noSecondPersonImperatives := 122 }

/-- WALS Ch 71 distribution: prohibitive types (n = 496). -/
structure ProhibitiveCounts where
  normalImpNormalNeg : Nat
  normalImpSpecialNeg : Nat
  specialImpNormalNeg : Nat
  specialImpSpecialNeg : Nat
  deriving Repr

def ProhibitiveCounts.total (c : ProhibitiveCounts) : Nat :=
  c.normalImpNormalNeg + c.normalImpSpecialNeg +
  c.specialImpNormalNeg + c.specialImpSpecialNeg

/-- Languages with any "special" prohibitive (Types 2, 3, 4). -/
def ProhibitiveCounts.special (c : ProhibitiveCounts) : Nat :=
  c.normalImpSpecialNeg + c.specialImpNormalNeg + c.specialImpSpecialNeg

/-- WALS Ch 71 counts (496 languages). -/
def ch71Distribution : ProhibitiveCounts :=
  { normalImpNormalNeg := 113
  , normalImpSpecialNeg := 182
  , specialImpNormalNeg := 55
  , specialImpSpecialNeg := 146 }

/-- WALS Ch 72 distribution: imperative-hortative systems (n = 375). The
    WALS coding splits languages by paradigm shape: maximal (full hortative+
    jussive), minimal (only the basic split), both, or neither. -/
structure ImpHortCounts where
  neitherTypeOfSystem : Nat
  minimalSystem : Nat
  maximalSystem : Nat
  bothTypesOfSystem : Nat
  deriving Repr

def ImpHortCounts.total (c : ImpHortCounts) : Nat :=
  c.neitherTypeOfSystem + c.minimalSystem +
  c.maximalSystem + c.bothTypesOfSystem

/-- WALS Ch 72 counts (375 languages). -/
def ch72Distribution : ImpHortCounts :=
  { neitherTypeOfSystem := 201
  , minimalSystem := 20
  , maximalSystem := 133
  , bothTypesOfSystem := 21 }

/-- WALS Ch 73 distribution: optative presence (n = 319). -/
structure OptativeCounts where
  present : Nat
  absent : Nat
  deriving Repr

def OptativeCounts.total (c : OptativeCounts) : Nat :=
  c.present + c.absent

/-- WALS Ch 73 counts (319 languages). -/
def ch73Distribution : OptativeCounts :=
  { present := 48
  , absent := 271 }

-- ============================================================================
-- Cross-linguistic generalizations: morphological imperative (Ch 70)
-- ============================================================================

/-- Languages with some morphological imperative (426/548 = 77.7%) vastly
    outnumber those without (122/548 = 22.3%): the former exceed the latter
    by more than 3:1. -/
theorem morph_imp_dominant :
    ch70Distribution.withMorphImp >
    ch70Distribution.noSecondPersonImperatives * 3 := by decide

/-- Two-number imperatives (singular and plural distinguished) are the single
    most common Ch 70 type: 292 of 548 languages. -/
theorem sg_pl_most_common :
    ch70Distribution.secondSingularAndSecondPlural >
      ch70Distribution.secondPersonNumberNeutral ∧
    ch70Distribution.secondSingularAndSecondPlural >
      ch70Distribution.noSecondPersonImperatives ∧
    ch70Distribution.secondSingularAndSecondPlural >
      ch70Distribution.secondSingular ∧
    ch70Distribution.secondSingularAndSecondPlural >
      ch70Distribution.secondPlural := by decide

-- ============================================================================
-- Cross-linguistic generalizations: prohibitives (Ch 71)
-- ============================================================================

/-- van der Auwera's key finding: the majority of languages (383/496 = 77.2%)
    use a special prohibitive construction (Types 2, 3, or 4). Only 113/496
    (22.8%) use Type 1 (normal imperative + normal negation). Prohibitives are
    typologically marked relative to affirmative imperatives. -/
theorem prohibitive_mostly_special :
    ch71Distribution.special > ch71Distribution.normalImpNormalNeg * 3 := by decide

/-- Type 2 (normal imperative + special negation) is the single most common
    prohibitive type, followed by Type 4, then Type 1, then Type 3. -/
theorem type2_most_common_prohibitive :
    ch71Distribution.normalImpSpecialNeg >
      ch71Distribution.specialImpSpecialNeg ∧
    ch71Distribution.specialImpSpecialNeg >
      ch71Distribution.normalImpNormalNeg ∧
    ch71Distribution.normalImpNormalNeg >
      ch71Distribution.specialImpNormalNeg := by decide

-- ============================================================================
-- Cross-linguistic generalizations: imperative-hortative systems (Ch 72)
-- ============================================================================

/-- More than half of languages (201/375 = 53.6%) have neither type of
    imperative-hortative system — i.e., the imperative paradigm does not
    extend morphologically to 1st-person hortative or 3rd-person jussive. -/
theorem neither_system_majority :
    ch72Distribution.neitherTypeOfSystem * 2 > ch72Distribution.total := by decide

/-- Minimal systems (only one of hortative/jussive) are the rarest type. -/
theorem minimal_system_rarest :
    ch72Distribution.minimalSystem < ch72Distribution.bothTypesOfSystem ∧
    ch72Distribution.minimalSystem < ch72Distribution.maximalSystem ∧
    ch72Distribution.minimalSystem < ch72Distribution.neitherTypeOfSystem := by
  decide

/-- Maximal systems (full hortative + jussive paradigm) are much more common
    than minimal or both-types systems. -/
theorem maximal_more_common_than_minimal :
    ch72Distribution.maximalSystem >
      ch72Distribution.minimalSystem + ch72Distribution.bothTypesOfSystem := by
  decide

-- ============================================================================
-- Cross-linguistic generalization: optatives (Ch 73)
-- ============================================================================

/-- Dedicated optatives are a minority feature: 271 of 319 languages lack one,
    outnumbering those with optatives by more than 5:1. -/
theorem optative_minority :
    ch73Distribution.absent > ch73Distribution.present * 5 := by decide

end Typology
