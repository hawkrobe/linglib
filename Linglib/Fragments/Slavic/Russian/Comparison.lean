import Linglib.Syntax.Comparative

/-!
# Russian comparative data

Russian compares with *X Adj-ee, chem Y*: the particle *chem* marks the
standard (WALS Ch 121A: particle, [stassen-2013]); a bare genitive standard
(*X Adj-ee Y-GEN*) is also available, its anatomy unrecorded here pending a
source for its Stassen classification. Degree is marked by the bound affix
*-ee* ~ *-ej*; the superlative is morphological.
-/

set_option autoImplicit false

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
