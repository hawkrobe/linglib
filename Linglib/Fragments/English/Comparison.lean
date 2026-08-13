import Linglib.Syntax.Comparative

/-!
# English comparative data

English compares with *X is taller than Y* / *X is more Adj than Y*: the
particle *than* marks the standard (WALS Ch 121A: particle, [stassen-2013]),
degree is marked by the free word *more* or the bound affix *-er*, and the
superlative is morphological (*-est*).
-/

set_option autoImplicit false

namespace English.Comparison

open Comparative

/-- The *than*-comparative: particle-marked standard, *more* or *-er* degree. -/
def than : Comparative :=
  { standardMarker := some "than"
  , caseAssignment := .derived
  , degreeMarker := some "more / -er"
  , degreeMorphology := true }

/-- Free degree word *more* alongside the affix *-er*. -/
def degreeWord : DegreeWordType := .hasDegreeWord

/-- Morphological superlative (*-est*). -/
def superlative : SuperlativeStrategy := .morphological

end English.Comparison
