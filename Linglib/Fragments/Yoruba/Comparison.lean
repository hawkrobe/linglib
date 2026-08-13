import Linglib.Syntax.Comparative

/-!
# Yoruba comparative data

Yoruba compares with *X Adj ju Y lọ* (WALS Ch 121A: exceed, [stassen-2013]):
the exceed verb *ju … lọ* takes the standard as its object. The adjective
carries no degree marking; superlative via exceeding a universal standard.
-/

set_option autoImplicit false

namespace Yoruba.Comparison

open Comparative

/-- The *ju … lọ* comparative: exceed verb taking the standard as object. -/
def ju : Comparative :=
  { standardMarker := some "ju...lo"
  , caseAssignment := .fixed
  , fixedEncoding := some .directObject }

/-- No degree marking on the adjective. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Superlative by exceeding a universal standard. -/
def superlative : SuperlativeStrategy := .exceedAll

end Yoruba.Comparison
