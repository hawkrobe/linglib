import Linglib.Typology.Comparison

/-!
# Finnish comparative profile
@cite{stassen-2013} @cite{wals-2013}

`ComparativeProfile` bundle for Finnish (ISO `fin`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
@cite{stassen-1985} 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Fragments.Finnish.Comparison

open _root_.Typology.Comparison

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

end Fragments.Finnish.Comparison
