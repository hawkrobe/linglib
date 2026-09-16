import Linglib.Syntax.RelativeClause.Basic

/-!
# Welsh relative-clause markers

The two relative particles of Welsh as [keenan-comrie-1977] records them (Section 1.3.2 and
Table 1): *a* introduces a postnominal clause with the relativized position deleted and covers
subjects and direct objects; *y* introduces a postnominal clause with a personal pronoun in the
relativized position and covers the positions from indirect object down.

## References

* [keenan-comrie-1977]
-/

namespace Welsh

open RelativeClause

/-- The particle *a*: postnominal, the relativized position deleted, subjects and direct objects.
[keenan-comrie-1977]'s (11a), *y bachgen a oedd yn darllen* 'the boy who was reading'. -/
def relParticleA : Marker :=
  { form := "a"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .postNominal
  , positions := {.subject, .directObject} }

/-- The particle *y*: postnominal, a personal pronoun in the relativized position, indirect
object through object of comparison. [keenan-comrie-1977]'s (11b), *dyma'r llyfr y darllenais y
stori ynddo* 'here is the book in which I read the story', with the pronoun in *ynddo* 'in it'. -/
def relParticleY : Marker :=
  { form := "y"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , placement := .postNominal
  , positions := {.indirectObject, .oblique, .genitive, .objComparison} }

/-- The Welsh relative-clause markers. -/
def relMarkers : List Marker := [relParticleA, relParticleY]

end Welsh
