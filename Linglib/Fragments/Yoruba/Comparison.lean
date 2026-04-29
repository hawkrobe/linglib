import Linglib.Typology.Comparison

/-!
# Yoruba comparative profile
@cite{stassen-2013} @cite{wals-2013}

`ComparativeProfile` bundle for Yoruba (ISO `yor`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Phenomena/Comparison/Studies/Stassen2013.lean`. The
@cite{stassen-1985} 6-way classification (where applicable) lives in
`Phenomena/Comparison/Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Fragments.Yoruba.Comparison

open _root_.Typology.Comparison

/-- Yoruba comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Yoruba"
  , iso := "yor"
  , comparativeType := .exceed
  , degreeWord := .noDegreeMarking
  , superlative := .exceedAll
  , comparativeForm := "X Adj ju Y lo"
  , standardMarker := "ju...lo"
  , degreeMarker := ""
  , basicOrder := "SVO" }

end Fragments.Yoruba.Comparison
