import Linglib.Syntax.Category.Coordinator

/-!
# Hausa coordinators

Hausa conjoins noun phrases with the free word *da* before the second coordinand. The same
word is the comitative preposition 'with', the source from which Haspelmath derives the
coordinator, citing Schwartz's data.

## Main definitions

* `Hausa.da`: the conjunctive coordinator.

## References

* [haspelmath-2007]
* [schwartz-1989]
-/

namespace Hausa

/-- *da* 'and', also the comitative 'with'. -/
def da : Coordinator :=
  { form := "da", gloss := "and; with", role := .conjunctive, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [da]

end Hausa
