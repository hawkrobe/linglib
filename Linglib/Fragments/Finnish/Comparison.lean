import Linglib.Syntax.Comparative

/-!
# Finnish comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for Finnish (ISO `fin`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Finnish.Comparison

open Comparative

/-- Finnish comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Finnish"
  , iso := "fin"
  , comparativeType := .locational
  , degreeWord := .morphological
  , superlative := .morphological
  , comparativeForm := "X on Y-tä Adj-mpi"
  , standardMarker := "partitive case"
  , degreeMarker := "-mpi (suffix)"
  , basicOrder := "SVO" }

end Finnish.Comparison
