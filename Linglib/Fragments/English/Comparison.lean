import Linglib.Syntax.Comparative

/-!
# English comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for English (ISO `eng`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace English.Comparison

open Comparative

/-- English comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "English"
  , iso := "eng"
  , comparativeType := .particle
  , degreeWord := .hasDegreeWord
  , superlative := .morphological
  , comparativeForm := "X is taller/more Adj than Y"
  , standardMarker := "than"
  , degreeMarker := "more / -er"
  , basicOrder := "SVO" }

end English.Comparison
