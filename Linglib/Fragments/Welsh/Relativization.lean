import Linglib.Syntax.Clause.Relative

/-!
# Welsh relative-clause markers

The two relative particles of Welsh as [keenan-comrie-1977] records them. The particle *a*
introduces a postnominal clause whose relativized position is deleted and relativizes subjects
and direct objects; the particle *y* introduces a postnominal clause with a personal pronoun at
the relativized position and relativizes the positions from indirect object down. The paper's
examples are *y bachgen a oedd yn darllen* 'the boy who was reading' and *dyma'r llyfr y
darllenais y stori ynddo* 'here is the book in which I read the story'.

## References

* [keenan-comrie-1977]
-/

namespace Welsh

open RelativeClause

/-- The relative particle *a* introduces a postnominal clause whose relativized position is
deleted; it relativizes subjects and direct objects. -/
def relParticleA : Marker :=
  { form := "a"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .postNominal
  , positions := {.subject, .directObject} }

/-- The relative particle *y* introduces a postnominal clause with a personal pronoun at the
relativized position; it relativizes the positions from indirect object down. -/
def relParticleY : Marker :=
  { form := "y"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , placement := .postNominal
  , positions := {.indirectObject, .oblique, .genitive, .objComparison} }

/-- The Welsh relative-clause markers. -/
def relMarkers : List Marker := [relParticleA, relParticleY]

end Welsh
