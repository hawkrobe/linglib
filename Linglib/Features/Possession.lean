/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Possession — typological feature substrate
[stassen-2009] [stassen-2013b] [nichols-1986] [nichols-bickel-2013]
[nichols-bickel-2013c] [heine-1997] [heine-2009] [aikhenvald-2012] [wals-2013]

Theory-neutral classification substrate for possession, typing per-language
Fragment data and feeding the cross-linguistic theorems in
`Studies/NicholsBickel2013.lean`, `Studies/Heine1997.lean`, and
`Studies/KampanarouAlexiadou2026.lean`. Graduated from the (dissolving)
`Typology/` layer to `Features/` under a bare-root `Possession` namespace,
mirroring `Features/Case` and `Features/Person`.

## Dimensions

- `Obligatoriness` (WALS Ch 58A)
- `Classification` (WALS Ch 59A)
- `PredicativeStrategy` ([stassen-2009] four-way; [stassen-2013b] / WALS 117A
  five-way refinement)
- `AdnominalMarking` ([nichols-1986]; WALS Ch 24A [nichols-bickel-2013c])
- `AffixPosition` (WALS Ch 57A)
- `Notion` ([heine-1997]): semantic targets of possession
- `InalienabilityRank`: coarse cline of inalienability candidates
- `Source` ([heine-1997] / [heine-2009]): grammaticalization schemas
- `Alienability`: the neutral binary the typological `Classification`, the
  DM-structural `PossessionType`, and the V&J semantic `PossessionRelationType`
  all coarsen onto — the shared cut, named once.
- `PossessionProfile`: per-language bundle + derived predicates.

## Theory-laden caveats

Several enums encode **specific frameworks**, not field-wide consensus:

- **`PredicativeStrategy` is Stassen's predicative typology.** [stassen-2009]
  recognises four types (Have / Locational / With-Comitative / Topic); the
  Genitive type is the fifth, introduced in his WALS chapter ([stassen-2013b],
  WALS 117A), where Genitive and Locational group under "Oblique Possessive".
  [heine-1997] splits Genitive and Goal as separable schemas.

- **`Classification` (3-way) hides language-internal variation.** Mayan
  3-class systems and Hawaiian a/o-class systems both code as `threeOrMore`
  with analytical loss. A fine-grained split indexed by possessor and possessum
  class (the Oceanic / Mayan literature; [aikhenvald-2012]) is future substrate.

- **`Source`** ([heine-1997] / [heine-2009] event schemas) and
  **`PredicativeStrategy`** (Stassen) are **parallel typologies over the same
  data**; `predicativeSource` is the bridge — the right pattern for parallel
  substrates.
-/

set_option autoImplicit false

namespace Possession

/-- WALS Ch 58A: whether some nouns (typically kinship, body parts) require
    obligatory possessive marking. Unpossessed forms are either ungrammatical
    or require special "absolute" morphology. -/
inductive Obligatoriness where
  /-- Obligatory possessive inflection exists (e.g., Mohawk, Turkish, Hungarian, Navajo). -/
  | exists_
  /-- No obligatory possessive inflection (e.g., English, Mandarin, Russian, Finnish). -/
  | noObligatory
  /-- Possessive inflection exists but is never obligatory; data insufficient. -/
  | unclear
  deriving DecidableEq, Repr

/-- WALS Ch 59A: whether the language morphosyntactically distinguishes
    different classes of possession (typically alienable vs inalienable). -/
inductive Classification where
  /-- All nouns use the same possessive construction (e.g., English, Russian, Turkish). -/
  | noClassification
  /-- Two-way classification, typically alienable vs inalienable
      (e.g., Fijian, Hawaiian, many Oceanic and Amazonian languages). -/
  | twoWay
  /-- Three or more classes of possession distinguished. -/
  | threeOrMore
  deriving DecidableEq, Repr

/-- [stassen-2009] / [stassen-2013b] (WALS 117A): how a language expresses
    predicative (clausal) possession ("I have X"). The five strategies refine
    Stassen's four-way 2009 typology (the Genitive type is the WALS 117A
    addition); each corresponds to a different syntactic analysis of the
    possessor. -/
inductive PredicativeStrategy where
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

/-- [nichols-1986]; WALS Ch 24A [nichols-bickel-2013c]: how the possessive
    relation is marked within the NP ("my book", "John's house"). -/
inductive AdnominalMarking where
  /-- Head-marking: possessive marker on the possessed noun (head)
      (e.g., Hungarian `Janos kalap-ja`, Swahili `kitabu ch-ake`). -/
  | headMarking
  /-- Dependent-marking: possessive marker on the possessor
      (e.g., English `John's book`, Japanese `Tanaka-no hon`). -/
  | dependentMarking
  /-- Double-marking: both possessor and possessed noun marked
      (e.g., Turkish `Ali-nin kitab-i`, Georgian `kac-is saxl-i`). -/
  | doubleMarking
  /-- Juxtaposition: no overt marker; word-order only (WALS "no marking")
      (e.g., Vietnamese `nha toi` 'house I' = 'my house'). -/
  | juxtaposition
  deriving DecidableEq, Repr

/-- WALS Ch 57A: position of pronominal possessive affixes on the noun. -/
inductive AffixPosition where
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

/-- [heine-1997]: the semantic *targets* of possessive constructions — what
    kind of possessive relationship is expressed. Distinct from `Source`, which
    encodes the cognitive source (how the construction arose diachronically).
    Seven notions; the first five form an abstractness cline
    (physical < temporary < permanent < inalienable < abstract), plus two for
    inanimate possessors. -/
inductive Notion where
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

/-- A coarse cline of inalienability candidates: if a language draws an
    alienable/inalienable boundary, body-part and kinship terms are the first
    candidates for the inalienable class. The numeric `toNat` ranking is a
    coarse operationalization for comparison, **not** a claimed cross-linguistic
    universal — [nichols-1986] and the prototype-network view ([aikhenvald-2012])
    treat kinship and body-parts as co-central rather than strictly ranked. -/
inductive InalienabilityRank where
  | bodyPart
  | kinship
  | spatialRelation
  | partWhole
  | culturalItem
  | generalProperty
  deriving DecidableEq, Repr

/-- Numeric rank for comparison (higher = more likely to be inalienable).
    A coarse operationalization; see `InalienabilityRank`. -/
def InalienabilityRank.toNat : InalienabilityRank → Nat
  | .bodyPart        => 5
  | .kinship         => 4
  | .spatialRelation => 3
  | .partWhole       => 2
  | .culturalItem    => 1
  | .generalProperty => 0

/-- [heine-1997] / [heine-2009]: eight diachronic source schemas from which
    predicative possession constructions arise via grammaticalization. -/
inductive Source where
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
def predicativeSource : PredicativeStrategy → Source
  | .haveVerb       => .action
  | .locational     => .location
  | .genitiveDative => .goal
  | .topic          => .topic
  | .comitative     => .companion

/-! ### The neutral alienability cut -/

/-- The neutral alienable/inalienable cut. Lives low in `Features` so that the
    typological `Classification`, the DM-structural `PossessionType`
    (`Morphology/DM`), and the V&J semantic `PossessionRelationType`
    (`Semantics/Possessive`) can each coarsen onto it rather than re-stipulating
    the contrast. -/
inductive Alienability where
  | inalienable
  | alienable
  deriving DecidableEq, Repr

/-- A language draws the `Alienability` cut iff it morphosyntactically
    classifies possession at all. -/
def Classification.drawsAlienabilityCut : Classification → Bool
  | .noClassification => false
  | _                 => true

/-- The inalienable class is drawn from the top of the cline: ranks at or above
    a language's `cut` count as inalienable. Makes the implicational shape of
    the hierarchy explicit, with the cut as the per-language parameter. -/
def InalienabilityRank.alienabilityAt (cut : InalienabilityRank) :
    InalienabilityRank → Alienability :=
  fun r => if cut.toNat ≤ r.toNat then .inalienable else .alienable

/-! ### Per-language profile -/

/-- A language's possession profile across [wals-2013] chapters 57–59 and the
    additional typological dimensions of predicative ([stassen-2009]) and
    adnominal ([nichols-1986]) possession. -/
structure PossessionProfile where
  /-- Language name. -/
  language : String
  /-- Language family. -/
  family : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Ch 58: whether obligatory possessive inflection exists. -/
  obligatoryPossession : Obligatoriness
  /-- Ch 59: whether the language morphosyntactically classifies possession. -/
  possessiveClassification : Classification
  /-- Primary strategy for predicative possession ("I have X"). -/
  predicativeStrategy : PredicativeStrategy
  /-- Primary strategy for adnominal possession ("my book"). -/
  adnominalStrategy : AdnominalMarking
  /-- Ch 57: position of pronominal possessive affixes, if attested. -/
  affixPosition : Option AffixPosition := .none
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

end Possession
