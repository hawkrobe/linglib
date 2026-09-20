import Linglib.Syntax.Category.Coordinator

/-!
# English coordinators

English coordinates with free words that stand before the second coordinand: *and*, *or*, *but*
and, after a negative, *nor*. The emphatic constructions pair a distinct first word with the
plain coordinator: *both … and*, *either … or*, *neither … nor*.

## Main definitions

* `English.Coordination.and_`, `English.Coordination.or_`, `English.Coordination.but_`,
  `English.Coordination.nor_`: the conjunctive, disjunctive, adversative and negative
  coordinators.

## References

* [haspelmath-2007]
-/

namespace English.Coordination

/-- *and*, in the emphatic *both … and*. -/
def and_ : Coordinator :=
  { form := "and", gloss := "and", role := .conjunctive, kind := .free, correlative := true }

/-- *or*, in the emphatic *either … or*. -/
def or_ : Coordinator :=
  { form := "or", gloss := "or", role := .disjunctive, kind := .free, correlative := true }

/-- *but*. -/
def but_ : Coordinator :=
  { form := "but", gloss := "but", role := .adversative, kind := .free }

/-- *nor*, in the emphatic *neither … nor*. -/
def nor_ : Coordinator :=
  { form := "nor", gloss := "nor", role := .negative, kind := .free, correlative := true }

/-- The coordinators. -/
def allEntries : List Coordinator := [and_, or_, but_, nor_]

end English.Coordination
