module

public import Linglib.Syntax.Clause.Relative

/-!
# English relative clauses

English has two relative-clause strategies, both postnominal. The complementizer *that*, or
nothing at all, introduces a clause in which the relativized position is left empty, and it
relativizes subjects and direct objects. The relative pronouns *who*, *whom*, *which* and
*whose* code the relativized position by their form or by a pied-piped preposition, and they
relativize everything from indirect objects down to objects of comparison, though the paper
finds *the man who Mary is taller than* "rather uncomfortable". The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
-/

@[expose] public section

namespace English

open RelativeClause

/-- The complementizer *that*, or no marker at all, leaves the relativized position empty and
relativizes subjects and direct objects. -/
def relThat : Marker :=
  { form := "that/∅"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .postNominal
  , positions := {.subject, .directObject} }

/-- The relative pronouns *who*, *whom*, *which* and *whose* code the relativized position and
relativize everything from indirect objects down. -/
def relWhom : Marker :=
  { form := "who/whom/which/whose"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , placement := .postNominal
  , positions := {.indirectObject, .oblique, .genitive, .objComparison} }

/-- The English relative-clause markers. -/
def relMarkers : List Marker := [relThat, relWhom]

end English
