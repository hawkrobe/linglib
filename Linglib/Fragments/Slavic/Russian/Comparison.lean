import Linglib.Syntax.Comparative

/-!
# Russian comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for Russian (ISO `rus`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Russian.Comparison

open Comparative

/-- Russian comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Russian"
  , iso := "rus"
  , comparativeType := .particle
  , degreeWord := .morphological
  , superlative := .morphological
  , comparativeForm := "X Adj-ee, chem Y / X Adj-ee Y-GEN"
  , standardMarker := "chem / genitive case"
  , degreeMarker := "-ee/-ej (suffix)"
  , basicOrder := "SVO" }

end Russian.Comparison
