import Linglib.Syntax.Comparative

/-!
# Latin comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for Latin (ISO `lat`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Latin.Comparison

open Comparative

/-- Latin comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Latin"
  , iso := "lat"
  , comparativeType := .mixed
  , degreeWord := .morphological
  , superlative := .morphological
  , comparativeForm := "X Adj-ior Y-ABL / X Adj-ior quam Y"
  , standardMarker := "ablative case / quam"
  , degreeMarker := "-ior (suffix)"
  , basicOrder := "SOV" }

end Latin.Comparison
