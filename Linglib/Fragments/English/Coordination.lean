module

public import Linglib.Syntax.Category.Coordinator

/-!
# English coordinators

English coordinates with free words that stand before the second coordinand: *and*, *or*, *but*
and, after a negative, *nor*. The emphatic constructions pair a distinct first word with the
plain coordinator: *both … and*, *either … or*, *neither … nor*.

## Main definitions

* `English.Coordination.and_`, `English.Coordination.or_`, `English.Coordination.but_`,
  `English.Coordination.nor_`: the conjunctive, disjunctive, adversative and negative
  coordinators.
* `English.Coordination.bothAnd`, `English.Coordination.eitherOr`,
  `English.Coordination.neitherNor`: the emphatic constructions.

## References

* [haspelmath-2007]
-/

@[expose] public section

namespace English.Coordination

/-- *and*. -/
def and_ : Coordinator :=
  { form := "and", gloss := "and", role := .conjunctive, kind := .free }

/-- *or*. -/
def or_ : Coordinator :=
  { form := "or", gloss := "or", role := .disjunctive, kind := .free }

/-- *but*. -/
def but_ : Coordinator :=
  { form := "but", gloss := "but", role := .adversative, kind := .free }

/-- *nor*. -/
def nor_ : Coordinator :=
  { form := "nor", gloss := "nor", role := .negative, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [and_, or_, but_, nor_]

/-- *both … and*. -/
def bothAnd : Coordinator.Correlative := ⟨"both", and_.form, and_⟩

/-- *either … or*. -/
def eitherOr : Coordinator.Correlative := ⟨"either", or_.form, or_⟩

/-- *neither … nor*. -/
def neitherNor : Coordinator.Correlative := ⟨"neither", nor_.form, nor_⟩

/-- The emphatic constructions. -/
def correlatives : List Coordinator.Correlative := [bothAnd, eitherOr, neitherNor]

end English.Coordination
