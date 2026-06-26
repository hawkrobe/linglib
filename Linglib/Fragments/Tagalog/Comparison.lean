import Linglib.Syntax.Comparative

/-!
# Tagalog comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for Tagalog (ISO `tgl`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Tagalog.Comparison

open Comparative

/-- Tagalog comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , comparativeType := .exceed
  , degreeWord := .hasDegreeWord
  , superlative := .definiteComparative
  , comparativeForm := "mas Adj si X kaysa kay Y / higit na Adj si X"
  , standardMarker := "kaysa / higit sa"
  , degreeMarker := "mas (< Spanish) / higit"
  , basicOrder := "VSO" }

end Tagalog.Comparison
