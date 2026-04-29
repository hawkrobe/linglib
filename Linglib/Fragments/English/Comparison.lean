import Linglib.Typology.Comparison

/-!
# English comparative profile
@cite{stassen-2013} @cite{wals-2013}

`ComparativeProfile` bundle for English (ISO `eng`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Phenomena/Comparison/Studies/Stassen2013.lean`. The
@cite{stassen-1985} 6-way classification (where applicable) lives in
`Phenomena/Comparison/Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Fragments.English.Comparison

open _root_.Typology.Comparison

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

end Fragments.English.Comparison
