import Linglib.Syntax.Comparative

/-!
# Navajo comparative data

WALS Ch 121A codes Navajo as a locational comparative ([stassen-2013]);
[stassen-1985] classifies "Navaho" in the locative subtype. Adjectival
predicates carry no comparative degree morphology. The standard-marking
postposition is not recorded here.
-/

set_option autoImplicit false

namespace Navajo.Comparison

open Comparative

/-- No comparative degree morphology. -/
def degreeWord : DegreeWordType := .noDegreeMarking

end Navajo.Comparison
