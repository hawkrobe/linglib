import Linglib.Syntax.Category.Coordinator

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

## References

* [szabolcsi-2015]
* [mitrovic-sauerland-2016]
* [haspelmath-2007]
-/

namespace Hungarian.Coordination

/-- *és* 'and'. -/
def es : Coordinator :=
  { form := "és", gloss := "and", role := .conjunctive, kind := .free }

/-- *is* 'also, too', after each coordinand 'both … and'. -/
def is_ : Coordinator :=
  { form := "is", gloss := "also, too; and", role := .conjunctive, kind := .free,
    alsoAdditive := true, correlative := true }

/-- *vagy* 'or'. -/
def vagy : Coordinator :=
  { form := "vagy", gloss := "or", role := .disjunctive, kind := .free }

/-- *de* 'but'. -/
def de : Coordinator :=
  { form := "de", gloss := "but", role := .adversative, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [es, is_, vagy, de]

end Hungarian.Coordination
