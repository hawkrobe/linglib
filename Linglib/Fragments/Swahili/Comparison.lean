import Linglib.Syntax.Comparative

/-!
# Swahili comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for Swahili (ISO `swh`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Swahili.Comparison

open Comparative

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

end Swahili.Comparison
