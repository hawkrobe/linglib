import Linglib.Syntax.Category.Coordinator

/-!
# Korean coordinators

Korean coordinates noun phrases with the comitative particles *-(g)wa*, *-hago* and the casual
*-(i)rang* 'and, with' between the conjuncts, and with the delimiter *-do* 'also' after each
conjunct, as Sohn describes them. Mitrović and Sauerland take *-(i)rang* for the J particle and
*-do* for the μ particle of their decomposition of conjunction. Sohn writes *(k)wa*, *hako*,
*(i)lang* and *to*.

## Main definitions

* `Korean.Coordination.irang`, `Korean.Coordination.to_` — the two particles

## References

* [mitrovic-2021]
* [mitrovic-sauerland-2016]
* [sohn-1994]
-/

namespace Korean.Coordination

/-- *-(i)rang* 'and, with', enclitic on the first conjunct, casual. -/
def irang : Coordinator :=
  { form := "-(i)rang", gloss := "and", role := .j, kind := .bound .after .clitic }

/-- *-to* 'and', enclitic on each conjunct, also the additive 'too'. -/
def to_ : Coordinator :=
  { form := "-to", gloss := "also, too; and", role := .mu, kind := .bound .after .clitic,
    alsoAdditive := true }

/-- The coordinators. -/
def allEntries : List Coordinator := [irang, to_]

end Korean.Coordination
