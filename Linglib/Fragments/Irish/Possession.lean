import Linglib.Features.Possession

/-!
# Irish possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for Irish (ISO `gle`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Irish.Possession

open _root_.Possession

/-- Irish possession profile. -/
def possession : PossessionProfile :=
  { language := "Irish"
  , family := "Indo-European"
  , iso := "gle"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .locational
  , adnominalStrategy := .dependentMarking
  , affixPosition := some .noAffix
  , examples := ["ta leabhar agam", "teach an fhir"]
  , notes := "Celtic at-possession: ta X ag-PRON; genitive case on possessor in adnominal" }

end Irish.Possession
