import Linglib.Core.Case.Basic

/-!
# Comparative Construction Entry

A structured entry for a language's comparative construction, parameterized
by `Core.Case` types. Used by Fragment files to encode how each language
marks the standard of comparison.

This structure captures @cite{stassen-1985}'s typological parameters:
case assignment (derived vs. fixed), fixed-case encoding (direct object vs.
adverbial), and the spatial case of the standard marker.
-/

namespace Core

open Core (CaseAssignment FixedCaseEncoding)

/-- A language's comparative construction entry.

    Encodes how the standard NP ('than X') is marked, following
    @cite{stassen-1985}'s classification parameters. -/
structure ComparativeEntry where
  /-- Case of the standard NP marker (from `Core.Case`). -/
  standardCase : Case
  /-- Whether standard NP case is derived from or independent of comparee. -/
  caseAssignment : CaseAssignment
  /-- For fixed-case: direct object or adverbial encoding. -/
  fixedEncoding : Option FixedCaseEncoding
  /-- Surface form of the standard marker. -/
  standardMarker : String
  /-- Whether the language has overt degree morphology on the adjective. -/
  hasDegreeMorphology : Bool
  deriving Repr, BEq

end Core
