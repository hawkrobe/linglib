module

public import Linglib.Syntax.Category.Coordinator

/-!
# Classical Tibetan coordinators

Classical Tibetan conjoins noun phrases with *-daŋ*, attached to the first coordinand, in the
example Haspelmath cites from Beyer; the form is a former case-marker meaning 'with'.

## Main definitions

* `ClassicalTibetan.Coordination.dang`: the conjunctive enclitic.

## References

* [haspelmath-2007]
* [beyer-1992]
-/

@[expose] public section

namespace ClassicalTibetan.Coordination

/-- *-daŋ* 'and', on the first coordinand, also 'with'. -/
def dang : Coordinator :=
  { form := "-daŋ", gloss := "and; with", role := .conjunctive, kind := .bound .after .clitic }

/-- The coordinators. -/
def allEntries : List Coordinator := [dang]

end ClassicalTibetan.Coordination
