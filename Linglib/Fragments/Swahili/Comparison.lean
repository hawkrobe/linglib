import Linglib.Syntax.Comparative

/-!
# Swahili comparative data

Swahili encodes comparison with *kuliko* or the verb *-zidi* 'exceed'
(WALS Ch 121A: exceed, [stassen-2013]); the adjective carries no degree
marking. Superlative via exceeding a universal standard.
-/

set_option autoImplicit false

namespace Swahili.Comparison

open Comparative

/-- No degree marking on the adjective. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Superlative by exceeding a universal standard. -/
def superlative : SuperlativeStrategy := .exceedAll

/-- Illustrative comparatives. -/
def comparativeForm : String := "X ni Adj kuliko Y / X anazidi Y kwa uAdj"

/-- The standard markers. -/
def standardMarker : String := "kuliko / -zidi"

end Swahili.Comparison
