import Linglib.Syntax.Comparative

/-!
# Arabic (MSA) comparative profile
[stassen-2013] [wals-2013]

`ComparativeProfile` bundle for Arabic (MSA) (ISO `arb`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Comparison.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Stassen2013Comparison.lean`. The
[stassen-1985] 6-way classification (where applicable) lives in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Arabic.ModernStandard.Comparison

open Comparative

/-- Arabic (MSA) comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "Arabic (MSA)"
  , iso := "arb"
  , comparativeType := .locational
  , degreeWord := .noDegreeMarking
  , superlative := .elative
  , comparativeForm := "X ʔafʕal min Y"
  , standardMarker := "min (from)"
  , degreeMarker := ""
  , basicOrder := "VSO/SVO" }

end Arabic.ModernStandard.Comparison
