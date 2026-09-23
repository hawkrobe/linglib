module

public import Linglib.Syntax.Category.Coordinator

/-!
# Latin coordinators

Latin conjoins with the free word *et* 'and', before the second coordinand, with the enclitic
*-que*, attached to the first word of the second coordinand as in *senatus populusque*, and with
the emphatic *atque*, *ac* before consonants. *Et* on the first coordinand answered by *-que*
on the second is emphatic, *et singulis universisque* 'both for individuals and for all
together'. The enclitic also builds the universal pronoun *quisque* 'each' on the
interrogative. Disjunction is *aut* or *vel*; negative coordination is *neque*, *nec*, repeated
for 'neither … nor'; and the adversative coordinator is *sed*.

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

@[expose] public section

namespace Latin.Coordination

/-- *et* 'and'. -/
def et : Coordinator :=
  { form := "et", gloss := "and", role := .conjunctive, kind := .free }

/-- *-que* 'and', enclitic in the second coordinand, also in *quisque* 'each'. -/
def que : Coordinator :=
  { form := "-que", gloss := "and", role := .conjunctive, kind := .bound .after .clitic,
    alsoQuantifier := true }

/-- *atque*, before consonants *ac*, 'and also'. -/
def atque : Coordinator :=
  { form := "atque", gloss := "and also", role := .conjunctive, kind := .free }

/-- *neque*, *nec* 'and not', repeated for 'neither … nor'. -/
def neque : Coordinator :=
  { form := "neque", gloss := "and not, nor", role := .negative, kind := .free }

/-- *aut* 'or'. -/
def aut : Coordinator :=
  { form := "aut", gloss := "or", role := .disjunctive, kind := .free }

/-- *vel* 'or'. -/
def vel : Coordinator :=
  { form := "vel", gloss := "or", role := .disjunctive, kind := .free }

/-- *sed* 'but'. -/
def sed : Coordinator :=
  { form := "sed", gloss := "but", role := .adversative, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [et, que, atque, neque, aut, vel, sed]

end Latin.Coordination
