import Linglib.Syntax.Comparative

/-!
# Russian comparative data

Russian marks the standard of comparison with the particle *chem* or the bare
genitive (WALS Ch 121A: particle, [stassen-2013]); degree is marked by the
bound affix *-ee* ~ *-ej*, and the superlative is morphological.
-/

set_option autoImplicit false

namespace Russian.Comparison

open Comparative

/-- Bound comparative affix *-ee* ~ *-ej*. -/
def degreeWord : DegreeWordType := .morphological

/-- Morphological superlative. -/
def superlative : SuperlativeStrategy := .morphological

/-- Illustrative comparatives (particle and genitive strategies). -/
def comparativeForm : String := "X Adj-ee, chem Y / X Adj-ee Y-GEN"

/-- The standard markers. -/
def standardMarker : String := "chem / genitive case"

/-- The bound comparative affix. -/
def degreeMarker : String := "-ee/-ej"

end Russian.Comparison
