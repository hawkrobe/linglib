import Linglib.Syntax.Comparative

/-!
# Latin comparative data

Latin has two productive comparative strategies: the particle *quam* and the
bare ablative standard. Latin is uncoded in WALS Ch 121A, so `comparativeType`
is coded here as `mixed`; [stassen-1985] classifies Latin as particle-primary
with a secondary separative option. Degree is marked by the bound affix *-ior*,
and the superlative is morphological.
-/

set_option autoImplicit false

namespace Latin.Comparison

open Comparative

/-- Mixed comparative (particle *quam* + ablative standard) — grammar-based
    coding; Latin is uncoded in WALS Ch 121A. -/
def comparativeType : ComparativeType := .mixed

/-- Bound comparative affix *-ior*. -/
def degreeWord : DegreeWordType := .morphological

/-- Morphological superlative. -/
def superlative : SuperlativeStrategy := .morphological

/-- Illustrative comparatives (ablative and particle strategies). -/
def comparativeForm : String := "X Adj-ior Y-ABL / X Adj-ior quam Y"

/-- The two standard-marking strategies. -/
def standardMarker : String := "ablative case / quam"

/-- The bound comparative affix. -/
def degreeMarker : String := "-ior"

end Latin.Comparison
