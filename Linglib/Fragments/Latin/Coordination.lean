import Linglib.Syntax.Category.Coordinator

/-!
# Latin coordinators

Latin conjoins with the free word *et* 'and', before the second coordinand, with the enclitic
*-que*, attached to the first word of the second coordinand as in *senatus populusque*, and with
the emphatic *atque*, *ac* before consonants. *Et* is repeated on each coordinand for 'both …
and', and *et* on the first coordinand may be answered by *-que* on the second. The enclitic also
builds the universal pronoun *quisque* 'each' on the interrogative. Disjunction is *aut* or
*vel*, each repeated for 'either … or'; negative coordination is *neque*, *nec*, repeated for
'neither … nor'; and the adversative coordinator is *sed*.

## Main definitions

* `Latin.Coordination.et`, `Latin.Coordination.que`, `Latin.Coordination.atque`: the
  conjunctive coordinators.
* `Latin.Coordination.aut`, `Latin.Coordination.vel`: the disjunctive coordinators.
* `Latin.Coordination.neque`, `Latin.Coordination.sed`: the negative and the adversative
  coordinator.

## References

* [haspelmath-2007]
* [mitrovic-sauerland-2016]
-/

namespace Latin.Coordination

/-- *et* 'and', repeated for 'both … and'. -/
def et : Coordinator :=
  { form := "et", gloss := "and", role := .conjunctive, kind := .free, correlative := true }

/-- *-que* 'and', enclitic in the second coordinand, also in *quisque* 'each'. -/
def que : Coordinator :=
  { form := "-que", gloss := "and", role := .conjunctive, kind := .bound .after .clitic,
    alsoQuantifier := true }

/-- *atque*, before consonants *ac*, 'and also'. -/
def atque : Coordinator :=
  { form := "atque", gloss := "and also", role := .conjunctive, kind := .free }

/-- *neque*, *nec* 'and not', repeated for 'neither … nor'. -/
def neque : Coordinator :=
  { form := "neque", gloss := "and not, nor", role := .negative, kind := .free,
    correlative := true }

/-- *aut* 'or', repeated for 'either … or'. -/
def aut : Coordinator :=
  { form := "aut", gloss := "or", role := .disjunctive, kind := .free, correlative := true }

/-- *vel* 'or', repeated for 'either … or'. -/
def vel : Coordinator :=
  { form := "vel", gloss := "or", role := .disjunctive, kind := .free, correlative := true }

/-- *sed* 'but'. -/
def sed : Coordinator :=
  { form := "sed", gloss := "but", role := .adversative, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [et, que, atque, neque, aut, vel, sed]

end Latin.Coordination
