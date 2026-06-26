import Linglib.Syntax.Comparative

/-!
# German comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for German (ISO `deu`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace German.Comparison

open Comparative

/-- German comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "German"
  , iso := "deu"
  , comparativeType := .particle
  , degreeWord := .morphological
  , superlative := .morphological
  , comparativeForm := "X ist größer als Y"
  , standardMarker := "als"
  , degreeMarker := "-er (suffix)"
  , basicOrder := "SVO/V2" }

end German.Comparison
