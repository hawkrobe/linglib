import Linglib.Typology.Possession

/-!
# Hungarian possession profile
@cite{stassen-2009} @cite{nichols-1986} @cite{heine-1997} 

PossessionProfile bundle for Hungarian (ISO `hun`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativePossession`, `AdnominalPossession`,
…) live in `Linglib/Typology/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Phenomena/Possession/Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Fragments.Hungarian.Possession

open _root_.Typology.Possession

/-- Hungarian possession profile. -/
def possession : PossessionProfile :=
  { language := "Hungarian"
  , family := "Uralic"
  , iso := "hun"
  , obligatoryPossession := .exists_
  , possessiveClassification := .noClassification
  , predicativeStrategy := .locational
  , adnominalStrategy := .headMarking
  , affixPosition := some .suffixes
  , examples := ["nekem van konyvem", "Janos kalap-ja"]
  , notes := "Dative possessor + van 'exists' + head-marked possessum; possessive suffixes obligatory on relational nouns" }

end Fragments.Hungarian.Possession
