import Linglib.Typology.Comparison

/-!
# Swahili comparative profile
@cite{stassen-2013} @cite{wals-2013}

`ComparativeProfile` bundle for Swahili (ISO `swh`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
@cite{stassen-1985} 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Fragments.Swahili.Comparison

open _root_.Typology.Comparison

/-- Swahili comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Swahili"
  , iso := "swh"
  , comparativeType := .exceed
  , degreeWord := .noDegreeMarking
  , superlative := .exceedAll
  , comparativeForm := "X ni Adj kuliko Y / X anazidi Y kwa uAdj"
  , standardMarker := "kuliko / -zidi"
  , degreeMarker := ""
  , basicOrder := "SVO" }

end Fragments.Swahili.Comparison
