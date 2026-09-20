import Linglib.Syntax.Category.Coordinator

/-!
# Hindi-Urdu coordinators

Hindi-Urdu conjoins with the free word *aur* 'and' before the second coordinand. The additive
particle *bhii* 'also, too' follows the phrase it associates with, and repeated after each
coordinand gives 'both … and'.

## Main definitions

* `HindiUrdu.Coordination.aur`, `HindiUrdu.Coordination.bhii`: the conjunctive coordinator and
  the additive particle that conjoins when repeated.

## TODO

The entries have not been checked against a grammar of Hindi-Urdu.
-/

namespace HindiUrdu.Coordination

/-- *aur* 'and'. -/
def aur : Coordinator :=
  { form := "aur", gloss := "and", role := .conjunctive, kind := .free }

/-- *bhii* 'also, too', after each coordinand 'both … and'. -/
def bhii : Coordinator :=
  { form := "bhii", gloss := "also, too; and", role := .conjunctive, kind := .free,
    alsoAdditive := true, correlative := true }

/-- The coordinators. -/
def allEntries : List Coordinator := [aur, bhii]

end HindiUrdu.Coordination
