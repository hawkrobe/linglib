module

public import Linglib.Syntax.Category.Coordinator

/-!
# Korean coordinators

Korean coordinates noun phrases with the comitative particles *-(g)wa*, *-hago* and the casual
*-(i)rang* 'and, with' between the conjuncts, and with the delimiter *-do* 'also' after each
conjunct, as Sohn describes them. Mitrović and Sauerland take *-(i)rang* for the J particle and
*-do* for the μ particle of their decomposition of conjunction. Sohn writes *(k)wa*, *hako*,
*(i)lang* and *to*.

## Main definitions

* `Korean.Coordination.irang`, `Korean.Coordination.do_` — the comitative *-(i)rang* 'and'
  and the additive *-do* 'also', Mitrović and Sauerland's J and μ particles
* `Korean.Coordination.hago`, `Korean.Coordination.doDo` — the comitative *-hago* and the
  emphatic *-do … -do* that Haspelmath sets against it

## References

* [haspelmath-2007]
* [mitrovic-2021]
* [mitrovic-sauerland-2016]
* [sohn-1994]
-/

@[expose] public section

namespace Korean.Coordination

/-- *-(i)rang* 'and', enclitic on the first conjunct, casual; also the casual comitative of
`Korean.Case.wa`. -/
def irang : Coordinator :=
  { morph := .encl "(i)rang", gloss := "and", role := .conjunctive }

/-- *-do* 'and', Sohn's *-to*, enclitic on each conjunct, also the additive 'too'. -/
def do_ : Coordinator :=
  { morph := .encl "do", gloss := "also, too; and", role := .conjunctive, alsoAdditive := true }

/-- *-hago* 'and', Sohn's *-hako*, enclitic on the first conjunct; also the comitative of
`Korean.Case.wa`. -/
def hago : Coordinator :=
  { morph := .encl "hago", gloss := "and", role := .conjunctive }

/-- The coordinators. -/
def allEntries : List Coordinator := [irang, hago, do_]

/-- *-do … -do* 'both … and', which Haspelmath sets against the single coordinator *-hago*. -/
def doDo : Coordinator.Correlative := ⟨[do_.morph], [do_.morph], hago⟩

/-- The emphatic constructions. -/
def correlatives : List Coordinator.Correlative := [doDo]

end Korean.Coordination
