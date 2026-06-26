import Linglib.Syntax.Comparative

/-!
# Yoruba comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for Yoruba (ISO `yor`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Yoruba.Comparison

open Comparative

/-- Yoruba comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Yoruba"
  , iso := "yor"
  , comparativeType := .exceed
  , degreeWord := .noDegreeMarking
  , superlative := .exceedAll
  , comparativeForm := "X Adj ju Y lo"
  , standardMarker := "ju...lo"
  , degreeMarker := ""
  , basicOrder := "SVO" }

end Yoruba.Comparison
