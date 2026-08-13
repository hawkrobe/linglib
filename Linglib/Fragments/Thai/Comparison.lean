import Linglib.Syntax.Comparative

/-!
# Thai comparative data

Thai encodes comparison with *kwàa* 'exceed' after the predicate
(WALS Ch 121A: exceed, [stassen-2013]); the adjective carries no degree
marking. Superlative via exceeding a universal standard.
-/

set_option autoImplicit false

namespace Thai.Comparison

open Comparative

/-- No degree marking on the adjective. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Superlative by exceeding a universal standard. -/
def superlative : SuperlativeStrategy := .exceedAll

/-- Illustrative comparative. -/
def comparativeForm : String := "X Adj kwaa Y"

/-- The exceed marker. -/
def standardMarker : String := "kwaa"

end Thai.Comparison
