import Linglib.Syntax.Category.Coordinator

/-!
# Yoruba coordinators

Yoruba conjoins noun phrases with the free word *àtí* before the second coordinand. Repeated
before each coordinand, *àtí A àtí B*, it gives the emphatic 'both … and', the construction
Haspelmath cites from Rowlands.

## Main definitions

* `Yoruba.Coordination.ati`: the conjunctive coordinator.

## References

* [haspelmath-2007]
* [rowlands-1969]
-/

namespace Yoruba.Coordination

/-- *àtí* 'and', repeated for 'both … and'. -/
def ati : Coordinator :=
  { form := "àtí", gloss := "and", role := .conjunctive, kind := .free, correlative := true }

/-- The coordinators. -/
def allEntries : List Coordinator := [ati]

end Yoruba.Coordination
