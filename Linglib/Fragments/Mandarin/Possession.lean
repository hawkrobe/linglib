import Linglib.Features.Possession

/-!
# Mandarin possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for Mandarin (ISO `cmn`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Mandarin.Possession

open _root_.Possession

/-- Mandarin possession profile. -/
def possession : PossessionProfile :=
  { language := "Mandarin"
  , family := "Sino-Tibetan"
  , iso := "cmn"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .haveVerb
  , adnominalStrategy := .dependentMarking
  , affixPosition := some .none
  , examples := ["wo you yi-ben shu", "wo de shu", "wo mama"]
  , notes := "Have-verb you; de marks adnominal possession but drops with inalienable/close relations" }

end Mandarin.Possession
