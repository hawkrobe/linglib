import Linglib.Typology.Comparison

/-!
# Mandarin comparative profile
@cite{stassen-2013} @cite{wals-2013}

`ComparativeProfile` bundle for Mandarin (ISO `cmn`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
@cite{stassen-1985} 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Fragments.Mandarin.Comparison

open _root_.Typology.Comparison

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

end Fragments.Mandarin.Comparison
