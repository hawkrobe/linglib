import Linglib.Syntax.Category.Coordinator

/-!
# Korean coordinators

Korean coordinates noun phrases with the comitative particles *-(g)wa*, *-hago* and the casual
*-(i)rang* 'and, with' between the conjuncts, and with the delimiter *-do* 'also' after each
conjunct, as Sohn describes them. Mitrović and Sauerland take *-(i)rang* for the J particle and
*-do* for the μ particle of their decomposition of conjunction. Sohn writes *(k)wa*, *hako*,
*(i)lang* and *to*.

## Main definitions

* `Korean.Coordination.irang`, `Korean.Coordination.to_` — the comitative *-(i)rang* 'and'
  and the additive *-to* 'also', Mitrović and Sauerland's J and μ particles
* `Korean.Coordination.hako`, `Korean.Coordination.toTo` — the comitative *-hako* and the
  emphatic *-to … -to* that Haspelmath sets against it

## References

* [haspelmath-2007]
* [mitrovic-2021]
* [mitrovic-sauerland-2016]
* [sohn-1994]
-/

namespace Korean.Coordination

/-- *-(i)rang* 'and, with', enclitic on the first conjunct, casual. -/
def irang : Coordinator :=
  { form := "-(i)rang", gloss := "and", role := .conjunctive, kind := .bound .after .clitic }

/-- *-to* 'and', enclitic on each conjunct, also the additive 'too'. -/
def to_ : Coordinator :=
  { form := "-to", gloss := "also, too; and", role := .conjunctive, kind := .bound .after .clitic,
    alsoAdditive := true }

/-- *-hako* 'and, with', enclitic on the first conjunct, in Sohn's spelling. -/
def hako : Coordinator :=
  { form := "-hako", gloss := "and; with", role := .conjunctive, kind := .bound .after .clitic }

/-- The coordinators. -/
def allEntries : List Coordinator := [irang, hako, to_]

/-- *-to … -to* 'both … and', which Haspelmath sets against the single coordinator *-hako*. -/
def toTo : Coordinator.Correlative := ⟨to_.form, to_.form, hako⟩

/-- The emphatic constructions. -/
def correlatives : List Coordinator.Correlative := [toTo]

end Korean.Coordination
