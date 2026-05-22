import Linglib.Data.WALS.Aggregation
import Linglib.Data.WALS.Features.F57A
import Linglib.Data.WALS.Features.F58A
import Linglib.Data.WALS.Features.F58B
import Linglib.Data.WALS.Features.F59A

/-!
# Possession typology — substrate
@cite{stassen-2009} @cite{nichols-1986} @cite{nichols-bickel-2013}
@cite{heine-1997} @cite{wals-2013}

Per-language possession-typology substrate for Fragment import. Mirrors the
`Linglib/Typology/{Domain}.lean` pattern (Case, Phonology, WordOrder).

## Substrate enums

- `ObligatoryPossession` (WALS Ch 58A)
- `PossessiveClassification` (WALS Ch 59A)
- `PredicativePossession` (@cite{stassen-2009}): 5-way strategy typology
- `AdnominalPossession` (@cite{nichols-1986}): head/dep/double/juxtaposition
- `PossessiveAffixPosition` (WALS Ch 57A)
- `NumberOfPossessiveNouns` (WALS Ch 58B)
- `PossessiveNotion` (@cite{heine-1997} §2.3): 7-way semantic targets
- `InalienabilityRank`: hierarchy of inalienability candidates
- `PossessionSource` (@cite{heine-1997} Table 2.1): 8 grammaticalization schemas
- `PossessionProfile`: bundle struct + 6 helper predicates

## Theory-laden caveats

Several substrate enums encode **specific frameworks**, not theory-neutral
consensus, despite the file's substrate role:

- **`PredicativePossession` is Stassen 2009's 5-way typology**, not field
  consensus. Heine 1997 splits Genitive/Dative differently (Goal vs
  Genitive as separable schemas); Creissels (2013, 2019) challenges the
  Companion vs Locational boundary. WALS Ch 117A (Stassen 2013) endorses
  these 5 categories — defensible substrate, but not framework-neutral.

- **`PossessiveClassification` (3-way) hides substantial language-internal
  variation.** Chappell & McGregor 1996, Stolz et al. 2008, Aikhenvald &
  Dixon 2013 argue alienability is a continuum interacting with possessor
  animacy and possessum semantics. Mayan 3-class systems and Hawaiian
  a/o-class systems both code as `threeOrMore` with analytical loss.
  Future work: a `PossessiveSplit` substrate indexed by
  `(PossessorClass × PossessumClass)` for fine-grained Oceanic / Mayan /
  Daakaka systems.

- **`PossessionSource` (Heine 1997 8-way)** and **`PredicativePossession`**
  (Stassen) coexist as **parallel typologies over the same data**;
  `predicativeSource` is the bridge. This is the right pattern for parallel
  substrates (cf. Causation's Song-vs-Pylkkänen architecture).

## WALS aggregates

WALS chapter aggregate distributions (`ch58_distribution`,
`ch59_no_classification_plurality_wals`, etc.) live in this file at the
substrate layer per the project's "WALS goes to `Linglib/Typology/`" rule,
since they are theory-neutral facts about WALS data, not paper-specific
contributions. Cross-linguistic theorems consuming Fragment per-language
data live in `Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Typology.Possession

private abbrev ch57  := Data.WALS.F57A.allData
private abbrev ch58  := Data.WALS.F58A.allData
private abbrev ch58b := Data.WALS.F58B.allData
private abbrev ch59  := Data.WALS.F59A.allData

/-- WALS Ch 58A: whether some nouns (typically kinship, body parts) require
    obligatory possessive marking. Unpossessed forms are either ungrammatical
    or require special "absolute" morphology. -/
inductive ObligatoryPossession where
  /-- Obligatory possessive inflection exists (e.g., Mohawk, Turkish, Hungarian, Navajo). -/
  | exists_
  /-- No obligatory possessive inflection (e.g., English, Mandarin, Russian, Finnish). -/
  | noObligatory
  /-- Possessive inflection exists but is never obligatory; data insufficient. -/
  | unclear
  deriving DecidableEq, Repr

/-- WALS Ch 59A: whether the language morphosyntactically distinguishes
    different classes of possession (typically alienable vs inalienable). -/
inductive PossessiveClassification where
  /-- All nouns use the same possessive construction (e.g., English, Russian, Turkish). -/
  | noClassification
  /-- Two-way classification, typically alienable vs inalienable
      (e.g., Fijian, Hawaiian, many Oceanic and Amazonian languages). -/
  | twoWay
  /-- Three or more classes of possession distinguished. -/
  | threeOrMore
  deriving DecidableEq, Repr

/-- @cite{stassen-2009}: how a language expresses predicative (clausal)
    possession ("I have X"). The four major strategies correspond to
    different syntactic analyses of the possessor. -/
inductive PredicativePossession where
  /-- Have-verb: dedicated transitive verb 'have'
      (e.g., English `I have a book`, Mandarin `wo you yi-ben shu`). -/
  | haveVerb
  /-- Locational/Existential: existential construction with possessor in
      a locative/oblique case (e.g., Russian `u menja est' kniga`,
      Finnish `minulla on kirja`). -/
  | locational
  /-- Genitive/Dative predicate: possessor in genitive or dative with copula
      (e.g., Hindi `mere paas kitaab hai`, Irish `ta leabhar agam`,
      Arabic `indi kitaab`). -/
  | genitiveDative
  /-- Topic-comment: possessor topicalized, possessum in existential comment
      (e.g., Japanese `watashi-ni-wa hon-ga aru`). -/
  | topic
  /-- Conjunctional/Comitative: "I am with a book"
      (e.g., Bantu Swahili `nina kitabu` 'I-with book'). -/
  | comitative
  deriving DecidableEq, Repr

/-- @cite{nichols-1986}: how the possessive relation is marked within the NP
    ("my book", "John's house"). -/
inductive AdnominalPossession where
  /-- Head-marking: possessive marker on the possessed noun (head)
      (e.g., Hungarian `Janos kalap-ja`, Swahili `kitabu ch-ake`). -/
  | headMarking
  /-- Dependent-marking: possessive marker on the possessor
      (e.g., English `John's book`, Japanese `Tanaka-no hon`). -/
  | dependentMarking
  /-- Double-marking: both possessor and possessed noun marked
      (e.g., Turkish `Ali-nin kitab-i`, Georgian `kac-is saxl-i`). -/
  | doubleMarking
  /-- Juxtaposition: no overt marker; word-order only
      (e.g., Vietnamese `nha toi` 'house I' = 'my house'). -/
  | juxtaposition
  deriving DecidableEq, Repr

/-- WALS Ch 57A: position of pronominal possessive affixes on the noun. -/
inductive PossessiveAffixPosition where
  /-- Possessive prefixes (e.g., Swahili class-agreement prefixes, many Bantu/Papuan). -/
  | prefixes
  /-- Possessive suffixes (e.g., Turkish -im, Hungarian -m, Finnish -ni). -/
  | suffixes
  /-- Both prefixes and suffixes used. -/
  | both
  /-- No possessive affixes; possession marked by independent words/clitics
      (e.g., English my, Japanese no, Mandarin de). -/
  | none
  deriving DecidableEq, Repr

/-- WALS Ch 58B: how many nouns in the language function as possessive
    markers (e.g., English "property" used as a possessive classifier). -/
inductive NumberOfPossessiveNouns where
  /-- No possessive nouns reported. -/
  | noneReported
  /-- Exactly one possessive noun. -/
  | one
  /-- Two to four possessive nouns. -/
  | twoToFour
  /-- Five or more possessive nouns. -/
  | fiveOrMore
  deriving DecidableEq, Repr

/-- @cite{heine-1997} §2.3: the semantic *targets* of possessive constructions —
    what kind of possessive relationship is expressed. Distinct from
    `PossessionSource`, which encodes the cognitive source (how the
    construction arose diachronically). Seven notions ordered by increasing
    abstractness: physical < temporary < permanent < inalienable < abstract
    (plus two for inanimate possessors). -/
inductive PossessiveNotion where
  /-- Physical possession (e.g., "I have a pen in my hand"). -/
  | physical
  /-- Temporary possession (e.g., "I have a rental car"). -/
  | temporary
  /-- Permanent possession (e.g., "I have a house"). -/
  | permanent
  /-- Inalienable possession (e.g., "I have two sisters", "blue eyes"). -/
  | inalienable
  /-- Abstract possession (e.g., "I have a headache", "an idea"). -/
  | abstract
  /-- Inanimate inalienable (e.g., "The tree has branches"). -/
  | inanimateInalienable
  /-- Inanimate alienable (e.g., "The room has a window"). -/
  | inanimateAlienable
  deriving DecidableEq, Repr

/-- Abstractness ordering: higher = more abstract possessive notion. -/
def PossessiveNotion.abstractness : PossessiveNotion → Nat
  | .physical             => 0
  | .temporary            => 1
  | .permanent            => 2
  | .inalienable          => 3
  | .abstract             => 4
  | .inanimateInalienable => 5
  | .inanimateAlienable   => 6

/-- The inalienability hierarchy: if a language draws an alienable/inalienable
    boundary, the inalienable class is drawn from the top. Body parts and
    kinship terms are always the first candidates. -/
inductive InalienabilityRank where
  | bodyPart
  | kinship
  | spatialRelation
  | partWhole
  | culturalItem
  | generalProperty
  deriving DecidableEq, Repr

/-- Numeric rank for comparison (higher = more likely to be inalienable). -/
def InalienabilityRank.toNat : InalienabilityRank → Nat
  | .bodyPart        => 5
  | .kinship         => 4
  | .spatialRelation => 3
  | .partWhole       => 2
  | .culturalItem    => 1
  | .generalProperty => 0

/-- @cite{heine-1997} Table 2.1 / @cite{heine-2009} Table 29.5: eight diachronic
    source schemas from which predicative possession constructions arise via
    grammaticalization. -/
inductive PossessionSource where
  /-- Action: "X takes Y" → 'X has Y' (e.g., English `have` < OE `habban`). -/
  | action
  /-- Location: "Y is at X" → 'X has Y' (e.g., Finnish adessive, Russian `u`). -/
  | location
  /-- Companion: "X is with Y" → 'X has Y' (e.g., Swahili `-na`, Venda `na`). -/
  | companion
  /-- Genitive: "X's Y exists" → 'X has Y' (e.g., Turkish `Hasan-ın inek-i var`). -/
  | genitive
  /-- Goal: "Y exists for X" → 'X has Y' (e.g., Hindi `mere paas`, Irish `agam`). -/
  | goal
  /-- Source: "Y exists from X" → 'X has Y'. -/
  | source
  /-- Topic: "As for X, Y exists" → 'X has Y' (e.g., Japanese `watashi-ni-wa`). -/
  | topic
  /-- Equation: "Y is X's" → 'X has Y' (e.g., Scots Gaelic `is leam an leabhar`). -/
  | equation
  deriving DecidableEq, Repr

/-- Map predicative strategies to their likely grammaticalization source. -/
def predicativeSource : PredicativePossession → PossessionSource
  | .haveVerb       => .action
  | .locational     => .location
  | .genitiveDative => .goal
  | .topic          => .topic
  | .comitative     => .companion

/-- A language's possession profile across @cite{wals-2013} chapters 57–59
    and the additional typological dimensions of predicative
    (@cite{stassen-2009}) and adnominal (@cite{nichols-1986}) possession. -/
structure PossessionProfile where
  /-- Language name (matches `LanguageProfile.name` when bundled). -/
  language : String
  /-- Language family. -/
  family : String
  /-- ISO 639-3 code (matches `LanguageProfile.iso` when bundled). -/
  iso : String := ""
  /-- Ch 58: whether obligatory possessive inflection exists. -/
  obligatoryPossession : ObligatoryPossession
  /-- Ch 59: whether the language morphosyntactically classifies possession. -/
  possessiveClassification : PossessiveClassification
  /-- Primary strategy for predicative possession ("I have X"). -/
  predicativeStrategy : PredicativePossession
  /-- Primary strategy for adnominal possession ("my book"). -/
  adnominalStrategy : AdnominalPossession
  /-- Ch 57: position of pronominal possessive affixes, if attested. -/
  affixPosition : Option PossessiveAffixPosition := .none
  /-- Illustrative possessive forms or constructions. -/
  examples : List String := []
  /-- Notes on the possession system. -/
  notes : String := ""
  deriving Repr, DecidableEq

/-- Does a language have obligatory possessive inflection? -/
def PossessionProfile.hasObligatoryPossession (p : PossessionProfile) : Bool :=
  p.obligatoryPossession == .exists_

/-- Does a language morphosyntactically classify possession? -/
def PossessionProfile.hasClassification (p : PossessionProfile) : Bool :=
  p.possessiveClassification != .noClassification

/-- Does a language use a have-verb strategy? -/
def PossessionProfile.usesHaveVerb (p : PossessionProfile) : Bool :=
  p.predicativeStrategy == .haveVerb

/-- Does a language use a locational/existential strategy? -/
def PossessionProfile.usesLocational (p : PossessionProfile) : Bool :=
  p.predicativeStrategy == .locational

/-- Does a language use head-marking for adnominal possession? -/
def PossessionProfile.isHeadMarking (p : PossessionProfile) : Bool :=
  p.adnominalStrategy == .headMarking

/-- Does a language use dependent-marking for adnominal possession? -/
def PossessionProfile.isDependentMarking (p : PossessionProfile) : Bool :=
  p.adnominalStrategy == .dependentMarking

-- ============================================================================
-- §2. WALS converters (Ch 57A, 58A, 58B, 59A)
-- ============================================================================

/-- WALS Ch 57A → `PossessiveAffixPosition`. -/
def fromWALS57A : Data.WALS.F57A.PositionOfPronominalPossessiveAffixes →
    PossessiveAffixPosition
  | .possessivePrefixes  => .prefixes
  | .possessiveSuffixes  => .suffixes
  | .prefixesAndSuffixes => .both
  | .noPossessiveAffixes => .none

/-- WALS Ch 58A → `ObligatoryPossession`. WALS only encodes `exists`/`absent`;
    our substrate adds `.unclear` for languages with optional/disputed coding. -/
def fromWALS58A : Data.WALS.F58A.ObligatoryPossessiveInflection →
    ObligatoryPossession
  | .exists => .exists_
  | .absent => .noObligatory

/-- WALS Ch 58B → `NumberOfPossessiveNouns`. -/
def fromWALS58B : Data.WALS.F58B.NumberOfPossessiveNouns →
    NumberOfPossessiveNouns
  | .noneReported => .noneReported
  | .one          => .one
  | .twoToFour    => .twoToFour
  | .fiveOrMore   => .fiveOrMore

/-- WALS Ch 59A → `PossessiveClassification`. WALS distinguishes "3–5
    classes" from "more than 5"; we collapse both into `.threeOrMore`. -/
def fromWALS59A : Data.WALS.F59A.PossessiveClassification →
    PossessiveClassification
  | .noPossessiveClassification => .noClassification
  | .twoClasses                 => .twoWay
  | .threeToFiveClasses         => .threeOrMore
  | .moreThanFiveClasses        => .threeOrMore

-- ============================================================================
-- §3. WALS aggregate-distribution helpers
-- ============================================================================

/-! `WALSCount` + `WALSCount.totalOf` are imported from
    `Linglib/Data/WALS/Aggregation.lean` (shared with the other
    Typology files that consume WALS distributions). -/

open Data.WALS (WALSCount)

/-- Ch 58 distribution: obligatory possessive inflection (N = 244). -/
def ch58Counts : List WALSCount :=
  [ ⟨"Obligatory possessive inflection exists",
      (ch58.filter (·.value == .exists)).length⟩
  , ⟨"No obligatory possessive inflection",
      (ch58.filter (·.value == .absent)).length⟩ ]

/-- Ch 59 distribution: possessive classification (N = 243). WALS distinguishes
    "3–5" from "more than 5"; we collapse both into "Three or more classes". -/
def ch59Counts : List WALSCount :=
  [ ⟨"No possessive classification",
      (ch59.filter (·.value == .noPossessiveClassification)).length⟩
  , ⟨"Two-way distinction (alienable/inalienable)",
      (ch59.filter (·.value == .twoClasses)).length⟩
  , ⟨"Three or more classes",
      (ch59.filter (·.value == .threeToFiveClasses)).length +
      (ch59.filter (·.value == .moreThanFiveClasses)).length⟩ ]

/-- Ch 58B distribution: number of possessive nouns (N = 243). -/
def ch58bCounts : List WALSCount :=
  [ ⟨"None reported",
      (ch58b.filter (·.value == .noneReported)).length⟩
  , ⟨"One",
      (ch58b.filter (·.value == .one)).length⟩
  , ⟨"Two to four",
      (ch58b.filter (·.value == .twoToFour)).length⟩
  , ⟨"Five or more",
      (ch58b.filter (·.value == .fiveOrMore)).length⟩ ]

-- ============================================================================
-- §4. WALS aggregate sample-size + distribution theorems
-- ============================================================================



/-- Ch 58 has one more language than Ch 59 (244 vs 243; Panare is in 58 but
    not 59). -/
theorem ch58_ch59_sample_diff :
    WALSCount.totalOf ch58Counts = WALSCount.totalOf ch59Counts + 1 := by
  native_decide

/-- Ch 57 value distribution from WALS data. -/
theorem ch57_distribution :
    (ch57.filter (·.value == .possessivePrefixes)).length = 255 ∧
    (ch57.filter (·.value == .possessiveSuffixes)).length = 355 ∧
    (ch57.filter (·.value == .prefixesAndSuffixes)).length = 32 ∧
    (ch57.filter (·.value == .noPossessiveAffixes)).length = 260 := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Ch 58 value distribution from WALS data. -/
theorem ch58_distribution :
    (ch58.filter (·.value == .exists)).length = 43 ∧
    (ch58.filter (·.value == .absent)).length = 201 := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 59 value distribution from WALS data. -/
theorem ch59_distribution :
    (ch59.filter (·.value == .noPossessiveClassification)).length = 125 ∧
    (ch59.filter (·.value == .twoClasses)).length = 94 ∧
    (ch59.filter (·.value == .threeToFiveClasses)).length = 20 ∧
    (ch59.filter (·.value == .moreThanFiveClasses)).length = 4 := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Ch 58B value distribution from WALS data. -/
theorem ch58b_distribution :
    (ch58b.filter (·.value == .noneReported)).length = 233 ∧
    (ch58b.filter (·.value == .one)).length = 3 ∧
    (ch58b.filter (·.value == .twoToFour)).length = 4 ∧
    (ch58b.filter (·.value == .fiveOrMore)).length = 3 := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Ch 58B: vast majority of languages have no possessive nouns (233/243). -/
theorem ch58b_none_reported_dominant :
    (ch58b.filter (·.value == .noneReported)).length >
    (ch58b.filter (·.value == .one)).length +
    (ch58b.filter (·.value == .twoToFour)).length +
    (ch58b.filter (·.value == .fiveOrMore)).length := by native_decide

/-- Ch 57: possessive suffixes are the most common affix position. -/
theorem ch57_suffixes_most_common :
    (ch57.filter (·.value == .possessiveSuffixes)).length >
    (ch57.filter (·.value == .possessivePrefixes)).length := by native_decide

/-- Ch 58: languages without obligatory possession vastly outnumber those with
    it in WALS data (201 vs 43, > 4×). -/
theorem ch58_no_obligatory_majority_wals :
    (ch58.filter (·.value == .absent)).length >
    (ch58.filter (·.value == .exists)).length * 4 := by native_decide

/-- Ch 59: no-possessive-classification is the most common pattern (125/243),
    followed by two-way (94/243). -/
theorem ch59_no_classification_plurality_wals :
    (ch59.filter (·.value == .noPossessiveClassification)).length >
    (ch59.filter (·.value == .twoClasses)).length := by native_decide

end Typology.Possession
