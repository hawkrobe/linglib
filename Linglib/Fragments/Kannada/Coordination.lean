import Linglib.Syntax.Category.Coordinator

/-!
# Kannada coordinators

Kannada, a Dravidian language of southern India, conjoins noun phrases with the enclitic *-u*
on each coordinand, *Narahariy-u: So:maše:kharan-u:* 'Narahari and Somashekhara' in the
example Haspelmath cites from Sridhar. The same enclitic is the additive particle 'also'.

## Main definitions

* `Kannada.Coordination.u`: the conjunctive enclitic.

## References

* [haspelmath-2007]
* [sridhar-1990]
-/

namespace Kannada.Coordination

/-- *-u* 'and', enclitic on each coordinand, also the additive 'also'. -/
def u : Coordinator :=
  { form := "-u", gloss := "and; also", role := .conjunctive, kind := .bound .after .clitic,
    alsoAdditive := true, correlative := true }

/-- The coordinators. -/
def allEntries : List Coordinator := [u]

end Kannada.Coordination
