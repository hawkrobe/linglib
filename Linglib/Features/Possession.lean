/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Possession — typological feature substrate

Theory-neutral classification enums for possession, following the WALS
possession chapters ([wals-2013]). Per-language values are bare `def`s in
`Fragments/<Lang>/Possession.lean`, consumed by `Studies/NicholsBickel2013`,
`Studies/Heine1997`, and `Studies/KampanarouAlexiadou2026`. Bare-root
`Possession` namespace under `Features/`, like `Features/Case`.

## Main definitions

`Obligatoriness` and `Classification` (WALS 58A and 59A,
[nichols-bickel-2013]), `PredicativeStrategy` ([stassen-2009] four-way;
[stassen-2013b] adds Genitive), `AdnominalMarking` ([nichols-1986]; WALS 24A,
[nichols-bickel-2013c]), `Notion` and `Source` ([heine-1997], [heine-2009]),
`InalienabilityRank` ([aikhenvald-2012]), and the neutral `Alienability` cut.
Cross-linguistic aggregation uses a study-local row in
`Studies/NicholsBickel2013.lean`.

## Notes

These enums adopt specific frameworks, not field-wide consensus:
`PredicativeStrategy` is Stassen's typology (Genitive is his WALS 117A addition,
grouped with Locational as "Oblique Possessive"); `Classification` collapses
Mayan/Oceanic multi-class systems into `threeOrMore`; `Source` (Heine's event
schemas) and `PredicativeStrategy` are parallel typologies bridged by
`predicativeSource`.

## References

* [nichols-bickel-2013], [nichols-bickel-2013c], [wals-2013] — the WALS
  chapters (24A, 58A, 59A)
* [stassen-2009], [stassen-2013b] — predicative possession (WALS 117A)
* [nichols-1986] — head- vs dependent-marking
* [heine-1997], [heine-2009] — possessive notions and source schemas
* [aikhenvald-2012] — inalienability
-/

namespace Possession

/-- Whether some nouns (kinship, body parts) require possessive marking (WALS 58A). -/
inductive Obligatoriness where
  /-- Obligatory possessive inflection exists (Mohawk, Navajo). -/
  | exists_
  /-- No obligatory possessive inflection (English, Russian). -/
  | noObligatory
  /-- Inflection exists but is never obligatory; data insufficient. -/
  | unclear
  deriving DecidableEq, Repr

/-- Whether possession is morphosyntactically classified, typically by
    alienability (WALS 59A). -/
inductive Classification where
  /-- One construction for all nouns (English, Russian). -/
  | noClassification
  /-- Two-way, typically alienable vs inalienable (Ewe, Rapanui). -/
  | twoWay
  /-- Three or more possessive classes. -/
  | threeOrMore
  deriving DecidableEq, Repr

/-- Stassen's classification of how a language predicates possession
    ("I have X"), with the Genitive type added in WALS 117A. -/
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

/-- The locus of marking inside the possessive NP (WALS 24A). -/
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

/-- Heine's semantic targets of possession, as opposed to `Source`, the
    diachronic origin. -/
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

/-- Coarse inalienability cline, body parts and kinship ranking highest.
    `toNat` is an operationalization for comparison rather than a claimed
    universal, since Nichols and Aikhenvald treat kinship and body parts as
    co-central. -/
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

/-- Heine's diachronic source schemas of predicative possession. -/
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

/-- Coarsening of the cline that counts ranks at or above `cut` as
    inalienable. -/
def InalienabilityRank.alienabilityAt (cut : InalienabilityRank) :
    InalienabilityRank → Alienability :=
  fun r => if cut.toNat ≤ r.toNat then .inalienable else .alienable

end Possession
