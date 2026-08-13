import Linglib.Syntax.Comparative

/-!
# Modern Standard Arabic comparative data

MSA marks the standard of comparison with *min* 'from' (WALS Ch 121A:
locational, [stassen-2013]); the elative pattern *ʔafʕal* carries the
comparison, with no separate degree word. Superlative via the elative without a
comparison standard.
-/

set_option autoImplicit false

namespace Arabic.ModernStandard.Comparison

open Comparative

/-- The elative pattern carries comparison; no separate degree word. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Elative superlative. -/
def superlative : SuperlativeStrategy := .elative

/-- Illustrative comparative. -/
def comparativeForm : String := "X ʔafʕal min Y"

/-- The separative standard marker. -/
def standardMarker : String := "min (from)"

end Arabic.ModernStandard.Comparison
