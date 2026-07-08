import Linglib.Syntax.Comparative

/-!
# French comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for French (ISO `fra`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace French.Comparison

open Comparative

/-- French comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "French"
  , iso := "fra"
  , comparativeType := .particle
  , degreeWord := .hasDegreeWord
  , superlative := .definiteComparative
  , comparativeForm := "X est plus Adj que Y"
  , standardMarker := "que"
  , degreeMarker := "plus"
  , basicOrder := "SVO" }

end French.Comparison
