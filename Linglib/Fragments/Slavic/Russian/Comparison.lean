module

public import Linglib.Syntax.Comparative

/-!
# Russian comparison

Russian compares with *X Adj-ee, chem Y*: the particle *chem* marks the standard, the particle
comparative of WALS Ch 121A ([stassen-2013]). A bare genitive standard, *X Adj-ee Y-GEN*, is also
available and is not entered. Degree is marked by the bound affix *-ee* ~ *-ej*, and the
superlative is morphological.

## References

* [stassen-2013]
-/

@[expose] public section

namespace Russian.Comparison

open Comparative

/-- The *chem*-comparative: particle-marked standard. -/
def chem : Comparative :=
  { standardMarker := some "chem"
  , caseAssignment := .derived
  , degreeMarker := some "-ee/-ej"
  , degreeMorphology := true }

/-- Bound comparative affix *-ee* ~ *-ej*. -/
def degreeWord : DegreeWordType := .morphological

/-- Morphological superlative. -/
def superlative : SuperlativeStrategy := .morphological

end Russian.Comparison
