module

public import Linglib.Syntax.Category.Pronoun.Reflexive
public import Linglib.Syntax.Reciprocal
public import Linglib.Syntax.Category.Pronoun.Reciprocal

/-!
# Hungarian reciprocals

Hungarian expresses reciprocity with the pronoun *egymás* 'each other', the compound of the
numeral *egy* 'one' and the distributor *más* 'other', which fills the object position and
keeps the verb transitive, *a gyerekek látták egymást* 'the children saw each other', and with
the verbal suffix *-óz-*, which yields a monovalent verb, *János és Mari csókolóztak* 'János and
Mari kissed'. As Rákosi notes, *egymás* is invariable, showing no person or number
inflection, whereas the reflexive *maga* 'oneself' has a full paradigm, *maga* in the singular
and *maguk* in the plural; Hungarian has no grammatical gender, so neither shows gender. The
antecedents *egymás* tolerates are the matter of `Studies/Rakosi2019.lean`.

## Main definitions

* `Hungarian.Reciprocals.egymas`, `Hungarian.Reciprocals.ozSuffix`,
  `Hungarian.Reciprocals.markers`: the reciprocal pronoun, the verbal suffix and the marker
  inventory.
* `Hungarian.Reciprocals.maga`, `Hungarian.Reciprocals.maguk`: the third person reflexive.

## References

* [rakosi-2019]
* [nordlinger-2023]
* [siloni-2008]
-/

@[expose] public section

namespace Hungarian.Reciprocals

open Reciprocal

/-- The reciprocal pronoun *egymás* 'each other', invariable. -/
def egymas : ReciprocalPronoun := { form := "egymás", person := some .third, number := none }

/-- The reciprocal verbal suffix *-óz-*. -/
def ozSuffix : Marker := { form := "-óz-", strategy := .verbalAffix }

/-- The reciprocal markers. -/
def markers : Finset Marker := {ozSuffix, egymas.toMarker}

/-- The third person singular reflexive *maga*. -/
def maga : ReflexivePronoun := { form := "maga", person := some .third, number := some .singular }

/-- The third person plural reflexive *maguk*. -/
def maguk : ReflexivePronoun := { form := "maguk", person := some .third, number := some .plural }

end Hungarian.Reciprocals
