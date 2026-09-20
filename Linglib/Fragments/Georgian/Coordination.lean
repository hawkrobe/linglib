import Linglib.Syntax.Category.Coordinator

/-!
# Georgian coordinators

Georgian conjoins with the free word *da* 'and' before the second coordinand, and with the
enclitic *-c* 'also, too' on each coordinand; the two combine, the enclitic on each coordinand
with *da* between them, the three constructions that Bill and colleagues test with Georgian
children. Disjunction is *an* 'or' and the adversative coordinator is *magram* 'but'.

## Main definitions

* `Georgian.Coordination.da`, `Georgian.Coordination.c_`: the conjunctive coordinator and the
  additive enclitic that conjoins when repeated.
* `Georgian.Coordination.an`, `Georgian.Coordination.magram`: the disjunctive and the
  adversative coordinator.

## References

* [bill-etal-2025]
* [mitrovic-2021]
-/

namespace Georgian.Coordination

/-- *da* 'and'. -/
def da : Coordinator :=
  { form := "da", gloss := "and", role := .conjunctive, kind := .free }

/-- *-c* 'also, too', enclitic on each coordinand 'both … and'. -/
def c_ : Coordinator :=
  { form := "-c", gloss := "also, too; and", role := .conjunctive, kind := .bound .after .clitic,
    alsoAdditive := true }

/-- *an* 'or'. -/
def an : Coordinator :=
  { form := "an", gloss := "or", role := .disjunctive, kind := .free }

/-- *magram* 'but'. -/
def magram : Coordinator :=
  { form := "magram", gloss := "but", role := .adversative, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [da, c_, an, magram]

end Georgian.Coordination
