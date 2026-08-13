import Linglib.Syntax.Comparative

/-!
# Yoruba comparative data

Yoruba encodes comparison with the exceed verb *ju … lọ* (WALS Ch 121A: exceed,
[stassen-2013]); the adjective carries no degree marking. Superlative via
exceeding a universal standard.
-/

set_option autoImplicit false

namespace Yoruba.Comparison

open Comparative

/-- No degree marking on the adjective. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Superlative by exceeding a universal standard. -/
def superlative : SuperlativeStrategy := .exceedAll

/-- Illustrative comparative. -/
def comparativeForm : String := "X Adj ju Y lo"

/-- The exceed-verb standard marker. -/
def standardMarker : String := "ju...lo"

end Yoruba.Comparison
