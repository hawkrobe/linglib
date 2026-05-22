import Linglib.Typology.Comparison

/-!
# Thai comparative profile
@cite{stassen-2013} @cite{wals-2013}

`ComparativeProfile` bundle for Thai (ISO `tha`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
@cite{stassen-1985} 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Fragments.Thai.Comparison

open _root_.Typology.Comparison

/-- Thai comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Thai"
  , iso := "tha"
  , comparativeType := .exceed
  , degreeWord := .noDegreeMarking
  , superlative := .exceedAll
  , comparativeForm := "X Adj kwaa Y"
  , standardMarker := "kwaa"
  , degreeMarker := ""
  , basicOrder := "SVO" }

end Fragments.Thai.Comparison
