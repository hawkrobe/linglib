/-!
# Possession typology — type definitions
@cite{stassen-2009} @cite{nichols-1986} @cite{nichols-bickel-2013} @cite{wals-2013}

Type-level enums for cross-linguistic possession typology, extracted from
`Phenomena/Possession/Typology.lean` so that Fragments can import them
without violating the Fragments → Phenomena dependency rule. WALS data,
per-language profiles, and cross-linguistic theorems remain in
`Phenomena/Possession/Typology.lean`.

## Schema

- `ObligatoryPossession` (WALS Ch 58A): obligatory inflection, none, unclear
- `PossessiveClassification` (WALS Ch 59A): noClassification / twoWay / threeOrMore
- `PredicativePossession` (@cite{stassen-2009}): haveVerb / locational / genitiveDative / topic / comitative
- `AdnominalPossession` (@cite{nichols-1986}): headMarking / dependentMarking / doubleMarking / juxtaposition
- `PossessiveAffixPosition` (WALS Ch 57A): prefixes / suffixes / both / none
- `NumberOfPossessiveNouns` (WALS Ch 58B): noneReported / one / twoToFour / fiveOrMore
-/

set_option autoImplicit false

namespace Typology.Possession

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

end Typology.Possession
