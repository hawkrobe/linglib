import Linglib.Syntax.Comparative

/-!
# Tagalog comparative data

Tagalog compares with the Spanish-derived degree word *mas* plus the standard
marker *kaysa*, or with *higit* 'exceed'. Tagalog is uncoded in WALS Ch 121A;
`comparativeType` is coded here as `exceed` on the basis of *higit*, though the
*mas … kaysa* pattern is particle-like, so the coding is contestable. No
superlative strategy is recorded.
-/

set_option autoImplicit false

namespace Tagalog.Comparison

open Comparative

/-- Exceed comparative (*higit*) — grammar-based coding; Tagalog is uncoded in
    WALS Ch 121A, and the *mas … kaysa* pattern is particle-like. -/
def comparativeType : ComparativeType := .exceed

/-- Free degree words *mas* and *higit*. -/
def degreeWord : DegreeWordType := .hasDegreeWord

/-- Illustrative comparatives. -/
def comparativeForm : String := "mas Adj si X kaysa kay Y / higit na Adj si X"

/-- The standard markers. -/
def standardMarker : String := "kaysa / higit sa"

/-- The free degree words. -/
def degreeMarker : String := "mas / higit"

end Tagalog.Comparison
