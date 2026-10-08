module

public import Linglib.Syntax.Category.Coordinator

/-!
# Hungarian coordinators

Hungarian conjoins with the free word *és* 'and' before the second coordinand, and with the
particle *is* 'also, too' after each coordinand, *Kati is Mari is* 'both Kate and Mary'. The two
combine, *Kati is és Mari is*, as Szabolcsi reports. Disjunction is *vagy* 'or' and the
adversative coordinator is *de* 'but'. The emphatic conjunction is *mind … mind*.

## Main definitions

* `Hungarian.Coordination.es`, `Hungarian.Coordination.is_`: the conjunctive coordinator and
  the additive particle that conjoins when repeated.
* `Hungarian.Coordination.vagy`, `Hungarian.Coordination.de`: the disjunctive and the
  adversative coordinator.
* `Hungarian.Coordination.mindMind`: the emphatic conjunction.

## References

* [szabolcsi-2015]
* [mitrovic-sauerland-2016]
* [haspelmath-2007]
-/

@[expose] public section

namespace Hungarian.Coordination

/-- *és* 'and'. -/
def es : Coordinator :=
  { morph := .free "és", gloss := "and", role := .conjunctive }

/-- *is* 'also, too', after each coordinand 'both … and'. -/
def is_ : Coordinator :=
  { morph := .free "is", gloss := "also, too; and", role := .conjunctive, alsoAdditive := true }

/-- *vagy* 'or'. -/
def vagy : Coordinator :=
  { morph := .free "vagy", gloss := "or", role := .disjunctive }

/-- *de* 'but'. -/
def de : Coordinator :=
  { morph := .free "de", gloss := "but", role := .adversative }

/-- The coordinators. -/
def allEntries : List Coordinator := [es, is_, vagy, de]

/-- *mind … mind* 'both … and'. -/
def mindMind : Coordinator.Correlative := ⟨[.free "mind"], [.free "mind"], es⟩

/-- The emphatic constructions. -/
def correlatives : List Coordinator.Correlative := [mindMind]

end Hungarian.Coordination
