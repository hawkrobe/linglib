module

public import Linglib.Syntax.Category.Coordinator

/-!
# Lango coordinators

Lango, a Nilotic language of Uganda, conjoins noun phrases with the free word *kèdè* before
the second coordinand, *cây kèdè càk* 'tea and milk'. The same word is the comitative 'with',
and Haspelmath gives the construction, from Noonan's grammar, as an example of a
comitative-derived coordinator.

## Main definitions

* `Lango.Coordination.kede`: the conjunctive coordinator.

## References

* [haspelmath-2007]
* [noonan-1992]
-/

@[expose] public section

namespace Lango.Coordination

/-- *kèdè* 'and', also the comitative 'with'. -/
def kede : Coordinator :=
  { form := "kèdè", gloss := "and; with", role := .conjunctive, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [kede]

end Lango.Coordination
