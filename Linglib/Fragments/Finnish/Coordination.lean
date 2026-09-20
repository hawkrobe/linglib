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

## References

* [haspelmath-2007]
-/

namespace Finnish.Coordination

/-- *ja* 'and'. -/
def ja : Coordinator :=
  { form := "ja", gloss := "and", role := .conjunctive, kind := .free }

/-- *tai* 'or', in the emphatic *joko … tai*. -/
def tai : Coordinator :=
  { form := "tai", gloss := "or", role := .disjunctive, kind := .free, correlative := true }

/-- *vai* 'or' of alternative questions. -/
def vai : Coordinator :=
  { form := "vai", gloss := "or", role := .disjunctive, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [ja, tai, vai]

end Finnish.Coordination
