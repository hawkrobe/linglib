import Linglib.Syntax.Comparative

/-!
# Mandarin comparative data

Mandarin encodes comparison with the *bǐ* construction (WALS Ch 121A: exceed,
[stassen-2013]); the free degree word *gèng* 'even more' is available. No
superlative strategy is recorded: the free superlative word *zuì* fits none of
`SuperlativeStrategy`'s cases.
-/

set_option autoImplicit false

namespace Mandarin.Comparison

open Comparative

/-- Free degree word *gèng*. -/
def degreeWord : DegreeWordType := .hasDegreeWord

/-- Illustrative comparative. -/
def comparativeForm : String := "X bi Y Adj"

/-- The standard marker of the *bǐ* construction. -/
def standardMarker : String := "bi"

/-- The free degree word. -/
def degreeMarker : String := "geng"

end Mandarin.Comparison
