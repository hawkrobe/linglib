import Linglib.Syntax.Category.Coordinator

/-!
# Persian coordinators

Persian conjoins with the free word *va* 'and', an Arabic loan, before the second coordinand;
the colloquial form is the enclitic *o*. The additive particle *ham* 'also, too', repeated with
each coordinand, gives 'both … and'.

## Main definitions

* `Farsi.Coordination.va`, `Farsi.Coordination.ham`: the conjunctive coordinator and the
  additive particle that conjoins when repeated.

## TODO

The entries have not been checked against a grammar of Persian.
-/

namespace Farsi.Coordination

/-- *va* 'and', colloquially the enclitic *o*. -/
def va : Coordinator :=
  { form := "va", gloss := "and", role := .conjunctive, kind := .free }

/-- *ham* 'also, too', with each coordinand 'both … and'. -/
def ham : Coordinator :=
  { form := "ham", gloss := "also, too; and", role := .conjunctive, kind := .free,
    alsoAdditive := true, correlative := true }

/-- The coordinators. -/
def allEntries : List Coordinator := [va, ham]

end Farsi.Coordination
