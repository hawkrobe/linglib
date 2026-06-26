/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Possession — typological feature substrate
[stassen-2009] [stassen-2013b] [nichols-1986] [nichols-bickel-2013]
[nichols-bickel-2013c] [heine-1997] [heine-2009] [aikhenvald-2012] [wals-2013]

Theory-neutral classification enums for possession. Per-language values are
bare `def`s in `Fragments/<Lang>/Possession.lean`, consumed by
`Studies/NicholsBickel2013`, `Studies/Heine1997`, and
`Studies/KampanarouAlexiadou2026`. Bare-root `Possession` namespace under
`Features/`, like `Features/Case`.

## Main definitions

`Obligatoriness` (WALS 58A), `Classification` (59A), `AffixPosition` (57A),
`PredicativeStrategy` ([stassen-2009] four-way; [stassen-2013b] adds Genitive),
`AdnominalMarking` ([nichols-1986]), `Notion` and `Source` ([heine-1997]),
`InalienabilityRank`, and the neutral `Alienability` cut. Per-language values
are bare `def`s in `Fragments/<Lang>/Possession.lean`; cross-linguistic
aggregation uses a study-local row in `Studies/NicholsBickel2013.lean`.

## Notes

These enums adopt specific frameworks, not field-wide consensus:
`PredicativeStrategy` is Stassen's typology (Genitive is his WALS 117A addition,
grouped with Locational as "Oblique Possessive"); `Classification` collapses
Mayan/Oceanic multi-class systems into `threeOrMore`; `Source` (Heine's event
schemas) and `PredicativeStrategy` are parallel typologies bridged by
`predicativeSource`.
-/

set_option autoImplicit false

namespace Possession

/-- WALS 58A: whether some nouns (kinship, body parts) require possessive marking. -/
inductive Obligatoriness where
  /-- Obligatory possessive inflection exists (Mohawk, Navajo). -/
  | exists_
  /-- No obligatory possessive inflection (English, Russian). -/
  | noObligatory
  /-- Inflection exists but is never obligatory; data insufficient. -/
  | unclear
  deriving DecidableEq, Repr

/-- WALS 59A: whether possession is morphosyntactically classified (alienability). -/
inductive Classification where
  /-- One construction for all nouns (English, Russian). -/
  | noClassification
  /-- Two-way, typically alienable vs inalienable (Fijian, Hawaiian). -/
  | twoWay
  /-- Three or more possessive classes. -/
  | threeOrMore
  deriving DecidableEq, Repr

/-- How a language predicates possession ("I have X"); [stassen-2009] four-way,
    [stassen-2013b] (WALS 117A) adds Genitive. -/
inductive PredicativeStrategy where
  /-- Transitive 'have' verb (English, Mandarin). -/
  | haveVerb
  /-- Existential with possessor in a locative/oblique (Russian, Finnish, Irish, Hindi). -/
  | locational
  /-- Existential with possessor in the genitive, "X's Y exists" (Turkish `var`). -/
  | genitive
  /-- Possessor topicalized over an existential comment (Japanese). -/
  | topic
  /-- Comitative "I am with Y" (Swahili `-na`). -/
  | comitative
  deriving DecidableEq, Repr

/-- [nichols-1986]; WALS 24A [nichols-bickel-2013c]: locus of NP-internal marking. -/
inductive AdnominalMarking where
  /-- Marker on the possessed head noun (Hungarian, Swahili). -/
  | headMarking
  /-- Marker on the possessor (English `'s`, Japanese `no`). -/
  | dependentMarking
  /-- Both possessor and head marked (Turkish, Georgian). -/
  | doubleMarking
  /-- No overt marker; word order alone (WALS "no marking"; Vietnamese). -/
  | zeroMarking
  deriving DecidableEq, Repr

/-- WALS 57A: position of pronominal possessive affixes on the noun. -/
inductive AffixPosition where
  /-- Possessive prefixes (Bantu, many Papuan). -/
  | prefixes
  /-- Possessive suffixes (Turkish, Hungarian, Finnish). -/
  | suffixes
  /-- Both prefixes and suffixes. -/
  | both
  /-- No affixes; independent words/clitics (English `my`, Mandarin `de`). -/
  | noAffix
  deriving DecidableEq, Repr

/-- [heine-1997]: semantic targets of possession (vs `Source`, the diachronic origin). -/
inductive Notion where
  /-- Physical possession ("a pen in my hand"). -/
  | physical
  /-- Temporary possession ("a rental car"). -/
  | temporary
  /-- Permanent possession ("a house"). -/
  | permanent
  /-- Inalienable possession ("two sisters", "blue eyes"). -/
  | inalienable
  /-- Abstract possession ("a headache", "an idea"). -/
  | abstract
  /-- Inanimate inalienable ("the tree has branches"). -/
  | inanimateInalienable
  /-- Inanimate alienable ("the room has a window"). -/
  | inanimateAlienable
  deriving DecidableEq, Repr

/-- Coarse inalienability cline (body-part/kinship rank highest). `toNat` is an
    operationalization for comparison, not a claimed universal — [nichols-1986]
    and [aikhenvald-2012] treat kinship and body-parts as co-central. -/
inductive InalienabilityRank where
  | bodyPart
  | kinship
  | spatialRelation
  | partWhole
  | culturalItem
  | generalProperty
  deriving DecidableEq, Repr

/-- Numeric rank (higher = more likely inalienable); see `InalienabilityRank`. -/
def InalienabilityRank.toNat : InalienabilityRank → Nat
  | .bodyPart        => 5
  | .kinship         => 4
  | .spatialRelation => 3
  | .partWhole       => 2
  | .culturalItem    => 1
  | .generalProperty => 0

/-- [heine-1997] / [heine-2009]: diachronic source schemas of predicative possession. -/
inductive Source where
  /-- Action "X takes Y" (English `have` < OE `habban`). -/
  | action
  /-- Location "Y is at X" (Finnish adessive, Russian `u`). -/
  | location
  /-- Companion "X is with Y" (Swahili `-na`). -/
  | companion
  /-- Genitive "X's Y exists" (Turkish `var`). -/
  | genitive
  /-- Goal "Y exists for X" (Hindi, Irish). -/
  | goal
  /-- Source "Y exists from X". -/
  | source
  /-- Topic "as for X, Y exists" (Japanese). -/
  | topic
  /-- Equation "Y is X's" (Scots Gaelic). -/
  | equation
  deriving DecidableEq, Repr

/-- Likely grammaticalization source of each predicative strategy. -/
def predicativeSource : PredicativeStrategy → Source
  | .haveVerb   => .action
  | .locational => .location
  | .genitive   => .genitive
  | .topic      => .topic
  | .comitative => .companion

/-! ### The neutral alienability cut -/

/-- Neutral alienable/inalienable cut, low in `Features` so the typological
    `Classification`, DM `PossessionType`, and V&J `PossessionRelationType` can
    coarsen onto it instead of re-stipulating the contrast. -/
inductive Alienability where
  | inalienable
  | alienable
  deriving DecidableEq, Repr

/-- A language draws the alienability cut iff it classifies possession at all. -/
def Classification.drawsAlienabilityCut : Classification → Bool
  | .noClassification => false
  | _                 => true

/-- Coarsen the cline at a language's `cut`: ranks at or above `cut` are inalienable. -/
def InalienabilityRank.alienabilityAt (cut : InalienabilityRank) :
    InalienabilityRank → Alienability :=
  fun r => if cut.toNat ≤ r.toNat then .inalienable else .alienable

end Possession
