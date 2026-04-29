import Linglib.Typology.Possession

/-!
# Mandarin possession profile
@cite{stassen-2009} @cite{nichols-1986} @cite{heine-1997} 

PossessionProfile bundle for Mandarin (ISO `cmn`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativePossession`, `AdnominalPossession`,
…) live in `Linglib/Typology/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Phenomena/Possession/Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Fragments.Mandarin.Possession

open _root_.Typology.Possession

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

end Fragments.Mandarin.Possession
