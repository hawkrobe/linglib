import Linglib.Syntax.Category.Coordinator

/-!
# Finnish coordinators

Finnish coordinates with free words that stand before the second coordinand. Conjunction is
*ja* 'and', with the emphatic *sekä … että* 'both … and', neither member of which is the plain
coordinator. Disjunction distinguishes standard *tai* 'or', with the emphatic *joko … tai*
'either … or', from interrogative *vai*, which asks the hearer to choose between the
alternatives.

## Main definitions

* `Finnish.Coordination.ja`: the conjunctive coordinator.
* `Finnish.Coordination.tai`, `Finnish.Coordination.vai`: the standard and the interrogative
  disjunctive coordinator.
* `Finnish.Coordination.sekaEtta`, `Finnish.Coordination.jokoTai`: the emphatic constructions.

## References

* [haspelmath-2007]
-/

namespace Finnish.Coordination

/-- *ja* 'and'. -/
def ja : Coordinator :=
  { form := "ja", gloss := "and", role := .conjunctive, kind := .free }

/-- *tai* 'or'. -/
def tai : Coordinator :=
  { form := "tai", gloss := "or", role := .disjunctive, kind := .free }

/-- *vai* 'or' of alternative questions. -/
def vai : Coordinator :=
  { form := "vai", gloss := "or", role := .disjunctive, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [ja, tai, vai]

/-- *sekä … että* 'both … and'. -/
def sekaEtta : Coordinator.Correlative := ⟨"sekä", "että", ja⟩

/-- *joko … tai* 'either … or'. -/
def jokoTai : Coordinator.Correlative := ⟨"joko", tai.form, tai⟩

/-- The emphatic constructions. -/
def correlatives : List Coordinator.Correlative := [sekaEtta, jokoTai]

end Finnish.Coordination
