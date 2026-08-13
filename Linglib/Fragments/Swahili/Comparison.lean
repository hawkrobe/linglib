import Linglib.Syntax.Comparative

/-!
# Swahili comparative data

Swahili compares with *X ni Adj kuliko Y* (WALS Ch 121A: exceed,
[stassen-2013]): *kuliko*, grammaticalized from an exceed verb, takes the
standard as its object; the verbal variant *X anazidi Y* '-zidi exceed' is
also available. The adjective carries no degree marking; superlative via
exceeding a universal standard.
-/

set_option autoImplicit false

namespace Swahili.Comparison

open Comparative

/-- The *kuliko*-comparative: exceed-derived marker taking the standard as
    object; the *-zidi* verbal variant shares the anatomy. -/
def kuliko : Comparative :=
  { standardMarker := some "kuliko"
  , caseAssignment := .fixed
  , fixedEncoding := some .directObject }

/-- No degree marking on the adjective. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Superlative by exceeding a universal standard. -/
def superlative : SuperlativeStrategy := .exceedAll

end Swahili.Comparison
