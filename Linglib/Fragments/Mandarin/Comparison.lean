import Linglib.Syntax.Comparative

/-!
# Mandarin comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for Mandarin (ISO `cmn`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Mandarin.Comparison

open Comparative

/-- Mandarin comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Mandarin"
  , iso := "cmn"
  , comparativeType := .exceed
  , degreeWord := .hasDegreeWord
  , superlative := .definiteComparative
  , comparativeForm := "X bi Y Adj"
  , standardMarker := "bi"
  , degreeMarker := "geng"
  , basicOrder := "SVO" }

end Mandarin.Comparison
