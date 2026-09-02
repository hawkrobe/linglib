/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Possession: classification vocabulary

Three taxonomies of the possession relation and the locus of adnominal marking. `RelationType`
is the lexical taxonomy of [vikner-jensen-2002] (inherent, part-whole, agentive, control);
`Notion` is the semantic one of [heine-1997] (physical, temporary, permanent, inalienable,
abstract, and the two inanimate notions); `InalienabilityRank` is the inalienability cline of
[aikhenvald-2012], body parts and kinship ranking highest. `AdnominalMarking` is the
head-marking/dependent-marking contrast of [nichols-1986] applied to the possessive NP, for
varieties the WALS coding ([nichols-bickel-2013c]) does not reach. Per-language WALS values are
looked up in `Data/WALS/Features/`, never restated as substrate.

## References

* [vikner-jensen-2002]
* [heine-1997]
* [aikhenvald-2012]
* [nichols-1986], [nichols-bickel-2013c]
-/

namespace Possession

/-- Four-way lexical taxonomy of possession relations from [vikner-jensen-2002] §3.1.2 (their
Table 1), reproduced in [barker-2011]. The separate "pragmatic" interpretation is not lexical and
is not one of these. -/
inductive RelationType where
  /-- Inherent relation: lexically argument-structural (the teacher's class). -/
  | inherent
  /-- Part-whole relation (the girl's nose, the car's wheel). -/
  | partWhole
  /-- Agentive relation (the girl's poem = the poem the girl wrote). -/
  | agentive
  /-- Control relation: ownership or legal control (the girl's car). -/
  | control
  deriving DecidableEq, Repr

/-- Heine's semantic targets of possession ([heine-1997]). -/
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

/-- Coarse inalienability cline ([aikhenvald-2012]); body parts and kinship, which Nichols and
Aikhenvald treat as co-central, rank highest. -/
inductive InalienabilityRank where
  | bodyPart
  | kinship
  | spatialRelation
  | partWhole
  | culturalItem
  | generalProperty
  deriving DecidableEq, Repr

/-- The locus of marking inside the possessive NP ([nichols-1986]; WALS 24A). -/
inductive AdnominalMarking where
  /-- Marker on the possessed head noun. -/
  | headMarking
  /-- Marker on the possessor (English `'s`, Japanese `no`). -/
  | dependentMarking
  /-- Both possessor and head marked. -/
  | doubleMarking
  /-- No overt marker on either; juxtaposition alone. -/
  | noMarking
  deriving DecidableEq, Repr

end Possession
