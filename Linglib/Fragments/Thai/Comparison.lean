import Linglib.Syntax.Comparative

/-!
# Thai comparative data

Thai compares with *X Adj kwàa Y* (WALS Ch 121A: exceed, [stassen-2013]):
*kwàa* 'exceed' takes the standard as its object after the predicate. The
adjective carries no degree marking; superlative via exceeding a universal
standard.
-/

set_option autoImplicit false

namespace Thai.Comparison

open Comparative

/-- The *kwàa*-comparative: exceed marker taking the standard as object. -/
def kwaa : Comparative :=
  { standardMarker := some "kwaa"
  , caseAssignment := .fixed
  , fixedEncoding := some .directObject }

/-- No degree marking on the adjective. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Superlative by exceeding a universal standard. -/
def superlative : SuperlativeStrategy := .exceedAll

end Thai.Comparison
