module

public import Linglib.Syntax.Category.Coordinator

/-!
# Hausa coordinators

Hausa conjoins noun phrases with the free word *dà* before the second conjunct, *gidā dà mōtā* 'a
house and a car', and often before the first as well, *dà Bellò dà Mūsā* 'both Musa and Bello'
([newman-2000]). The same word is the comitative preposition 'with', the source from which
[haspelmath-2007] derives the coordinator, citing [schwartz-1989]'s data.

## Main definitions

* `Hausa.da`: the conjunctive coordinator.

## References

* [haspelmath-2007]
* [newman-2000]
* [schwartz-1989]
-/

@[expose] public section

namespace Hausa

/-- *dà* 'and', also the comitative 'with'. -/
def da : Coordinator :=
  { form := "dà", gloss := "and; with", role := .conjunctive, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [da]

end Hausa
