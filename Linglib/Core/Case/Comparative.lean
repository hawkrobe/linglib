import Linglib.Core.Case.Basic
/-!
# Comparative Entry
@cite{stassen-1985}

A typed record for the parameters of a comparative construction in a
particular language: standard case, how that case is assigned, optional
fixed-encoding role, the standard marker (e.g., *than*, *より*), and
whether the construction has dedicated degree morphology.
-/

namespace Core

/-- A language's comparative construction entry (@cite{stassen-1985}). -/
structure ComparativeEntry where
  standardCase : Case
  caseAssignment : CaseAssignment
  fixedEncoding : Option FixedCaseEncoding
  standardMarker : String
  hasDegreeMorphology : Bool
  deriving Repr, BEq

end Core
