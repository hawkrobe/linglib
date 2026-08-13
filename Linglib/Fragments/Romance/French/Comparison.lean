import Linglib.Syntax.Comparative

/-!
# French comparative data

French marks the standard of comparison with the particle *que* (WALS Ch 121A:
particle, [stassen-2013]) and degree with the free word *plus*; the superlative
is the definite article plus the comparative (*le plus grand*).
-/

set_option autoImplicit false

namespace French.Comparison

open Comparative

/-- Free degree word *plus*. -/
def degreeWord : DegreeWordType := .hasDegreeWord

/-- Definite article + comparative superlative. -/
def superlative : SuperlativeStrategy := .definiteComparative

/-- Illustrative comparative. -/
def comparativeForm : String := "X est plus Adj que Y"

/-- The comparative particle marking the standard. -/
def standardMarker : String := "que"

/-- The free degree word. -/
def degreeMarker : String := "plus"

end French.Comparison
