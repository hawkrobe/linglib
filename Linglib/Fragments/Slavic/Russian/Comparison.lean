import Linglib.Typology.Comparison

/-!
# Russian comparative profile
@cite{stassen-2013} @cite{wals-2013}

`ComparativeProfile` bundle for Russian (ISO `rus`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
@cite{stassen-1985} 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Fragments.Slavic.Russian.Comparison

open _root_.Typology.Comparison

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

end Fragments.Slavic.Russian.Comparison
