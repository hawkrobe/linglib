import Linglib.Typology.Comparison

/-!
# Navajo comparative profile
@cite{stassen-2013} @cite{wals-2013}

`ComparativeProfile` bundle for Navajo (ISO `nav`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
@cite{stassen-1985} 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Fragments.Navajo.Comparison

open _root_.Typology.Comparison

/-- Navajo comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Navajo"
  , iso := "nav"
  , comparativeType := .conjoined
  , degreeWord := .noDegreeMarking
  , superlative := .none
  , comparativeForm := "X nineez, Y altso"
  , standardMarker := ""
  , degreeMarker := ""
  , basicOrder := "SOV" }

end Fragments.Navajo.Comparison
