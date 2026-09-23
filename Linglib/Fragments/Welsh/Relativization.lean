module

public import Linglib.Syntax.Clause.Relative

/-!
# Welsh relative clauses

Welsh has two relative particles. *A* introduces a postnominal relative clause in which the
relativized position is left empty, and it relativizes subjects and direct objects: *y bachgen a
oedd yn darllen* 'the boy who was reading'. *Y* introduces a postnominal relative clause in which
the relativized position holds a personal pronoun, and it relativizes everything from indirect
objects down to objects of comparison: *dyma'r llyfr y darllenais y stori ynddo* 'here is the
book in which I read the story', with the pronoun in *ynddo* 'in it'. The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
-/

@[expose] public section

namespace Welsh

open RelativeClause

/-- The particle *a* leaves the relativized position empty and relativizes subjects and direct
objects. -/
def relParticleA : Marker :=
  { form := "a"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .postNominal
  , positions := {.subject, .directObject} }

/-- The particle *y* puts a personal pronoun in the relativized position and relativizes
everything from indirect objects down. -/
def relParticleY : Marker :=
  { form := "y"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , placement := .postNominal
  , positions := {.indirectObject, .oblique, .genitive, .objComparison} }

/-- The Welsh relative-clause markers. -/
def relMarkers : List Marker := [relParticleA, relParticleY]

end Welsh
