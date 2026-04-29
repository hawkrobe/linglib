import Linglib.Typology.Comparison

/-!
# German comparative profile
@cite{stassen-2013} @cite{wals-2013}

`ComparativeProfile` bundle for German (ISO `deu`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Phenomena/Comparison/Studies/Stassen2013.lean`. The
@cite{stassen-1985} 6-way classification (where applicable) lives in
`Phenomena/Comparison/Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Fragments.German.Comparison

open _root_.Typology.Comparison

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

end Fragments.German.Comparison
