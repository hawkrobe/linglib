import Linglib.Syntax.Category.Coordinator

/-!
# Korean coordinators

Korean coordinates noun phrases with enclitic particles: *-(i)rang* 'and' of the informal
register, with *-(k)wa* and *-hako* its more formal alternatives, and *-to* 'and' on each
conjunct, which is also the additive particle 'too'. Mitrović and Sauerland take *-(i)rang* for
the J particle and *-to* for the μ particle of their decomposition of conjunction.

## Main definitions

* `Korean.Coordination.irang`, `Korean.Coordination.to_` — the two particles

## References

* [mitrovic-2021]
* [mitrovic-sauerland-2016]
-/

namespace Korean.Coordination

/-- *-(i)rang* 'and', enclitic on the first conjunct, informal. -/
def irang : Coordinator :=
  { form := "-(i)rang", gloss := "and", role := .j, kind := .bound .after .clitic }

/-- *-to* 'and', enclitic on each conjunct, also the additive 'too'. -/
def to_ : Coordinator :=
  { form := "-to", gloss := "also, too; and", role := .mu, kind := .bound .after .clitic,
    alsoAdditive := true }

/-- The coordinators. -/
def allEntries : List Coordinator := [irang, to_]

end Korean.Coordination
