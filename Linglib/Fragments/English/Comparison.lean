import Linglib.Syntax.Comparative

/-!
# English comparative data

English marks the standard of comparison with the particle *than* (WALS Ch 121A:
particle, [stassen-2013]), degree with the free word *more* or the bound affix
*-er*, and the superlative morphologically (*-est*).
-/

set_option autoImplicit false

namespace English.Comparison

open Comparative

/-- Free degree word *more* alongside the affix *-er*. -/
def degreeWord : DegreeWordType := .hasDegreeWord

/-- Morphological superlative (*-est*). -/
def superlative : SuperlativeStrategy := .morphological

/-- Illustrative comparative. -/
def comparativeForm : String := "X is taller/more Adj than Y"

/-- The comparative particle marking the standard. -/
def standardMarker : String := "than"

/-- Degree markers: free word and bound affix. -/
def degreeMarker : String := "more / -er"

end English.Comparison
