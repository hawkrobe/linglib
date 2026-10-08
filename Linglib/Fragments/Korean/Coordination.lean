module

public import Linglib.Syntax.Category.Coordinator

/-!
# Korean coordinators

Korean coordinates noun phrases with the comitative particles, formal *-(g)wa* and informal *-hago*
and *-(i)rang*, 'and, with' between the conjuncts, and with the delimiter *-do* 'also' after each
conjunct, and disjoins them with *-(i)na* 'or', as Sohn describes them; *-hago* and *-(i)na* may be
repeated after the second conjunct ([sohn-1999], pp. 339–340). Mitrović and Sauerland take
*-(i)rang* for the J particle and *-do* for the μ particle of their decomposition of conjunction.
Sohn writes *(k)wa*, *hako*, *(i)lang* and *to*.

## Main definitions

* `Korean.Coordination.irang`, `Korean.Coordination.do_` — the comitative *-(i)rang* 'and'
  and the additive *-do* 'also', Mitrović and Sauerland's J and μ particles
* `Korean.Coordination.hago`, `Korean.Coordination.doDo` — the comitative *-hago* and the
  emphatic *-do … -do* that Haspelmath sets against it
* `Korean.Coordination.gwa`, `Korean.Coordination.ina` — the formal comitative *-(g)wa* 'and'
  and the disjunctive *-(i)na* 'or'

## References

* [haspelmath-2007]
* [mitrovic-2021]
* [mitrovic-sauerland-2016]
* [sohn-1994]
* [sohn-1999]
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

/-- *-hago* 'and', Sohn's *-hako*, informal, enclitic on the first conjunct and optionally the
second; also the comitative of `Korean.Case.wa`. -/
def hago : Coordinator :=
  { morph := .encl "hago", gloss := "and", role := .conjunctive }

/-- *-(g)wa* 'and', Sohn's *-(k)wa*, formal, enclitic on the first conjunct; also the comitative
of `Korean.Case.wa`. -/
def gwa : Coordinator :=
  { morph := .encl "(g)wa", gloss := "and", role := .conjunctive }

/-- *-(i)na* 'or', enclitic on the first disjunct and optionally the second. -/
def ina : Coordinator :=
  { morph := .encl "(i)na", gloss := "or", role := .disjunctive }

/-- The coordinators. -/
def allEntries : List Coordinator := [gwa, irang, hago, do_, ina]

/-- *-do … -do* 'both … and', which Haspelmath sets against the single coordinator *-hago*. -/
def doDo : Coordinator.Correlative := ⟨[do_.morph], [do_.morph], hago⟩

/-- The emphatic constructions. -/
def correlatives : List Coordinator.Correlative := [doDo]

end Korean.Coordination
