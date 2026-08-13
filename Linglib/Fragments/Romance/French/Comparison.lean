import Linglib.Syntax.Comparative

/-!
# French comparative data

French compares with *X est plus Adj que Y*: the particle *que* marks the
standard (WALS Ch 121A: particle, [stassen-2013]) and the free word *plus*
marks degree; the superlative is the definite article plus the comparative
(*le plus grand*).
-/

set_option autoImplicit false

namespace French.Comparison

open Comparative

/-- The *que*-comparative: particle-marked standard, free *plus* degree. -/
def que : Comparative :=
  { standardMarker := some "que"
  , caseAssignment := .derived
  , degreeMarker := some "plus" }

/-- Free degree word *plus*. -/
def degreeWord : DegreeWordType := .hasDegreeWord

/-- Definite article + comparative superlative. -/
def superlative : SuperlativeStrategy := .definiteComparative

end French.Comparison
