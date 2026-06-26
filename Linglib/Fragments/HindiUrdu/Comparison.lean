import Linglib.Syntax.Comparative

/-!
# Hindi-Urdu comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for Hindi-Urdu (ISO `hin`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace HindiUrdu.Comparison

open Comparative

/-- Hindi-Urdu comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , comparativeType := .locational
  , degreeWord := .hasDegreeWord
  , superlative := .comparativeUniversal
  , comparativeForm := "X Y se (zyaadaa) Adj hai"
  , standardMarker := "se"
  , degreeMarker := "zyaadaa"
  , basicOrder := "SOV" }

end HindiUrdu.Comparison
