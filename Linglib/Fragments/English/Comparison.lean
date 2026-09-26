module

public import Linglib.Syntax.Comparative

/-!
# English comparison

English compares with a particle marking the standard, *X is taller than Y*, *X is more
careful than Y*: the standard follows *than*, whose case is derived from the comparee's, and the
degree is marked on the adjective, by the suffix *-er* or the free word *more*. The
superlative is morphological, *-est*. Stassen classes the construction as a particle
comparative.

## Main definitions

* `English.Comparison.than`: the *than*-comparative.
* `English.Comparison.degreeWord`, `English.Comparison.superlative`: the degree word and the
  superlative strategy.

## References

* [stassen-1985]
* [stassen-2013]
-/

@[expose] public section

namespace English.Comparison

open Comparative

/-- The *than*-comparative, with a particle-marked standard and the degree marked by *more* or
*-er*. -/
def than : Comparative :=
  { standardMarker := some "than", caseAssignment := .derived, degreeMarker := some "more / -er",
    degreeMorphology := true }

/-- English has the free degree word *more* beside the suffix *-er*. -/
def degreeWord : DegreeWordType := .hasDegreeWord

/-- The superlative is morphological, *-est*. -/
def superlative : SuperlativeStrategy := .morphological

end English.Comparison
