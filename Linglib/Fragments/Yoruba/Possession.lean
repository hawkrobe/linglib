import Linglib.Typology.Possession

/-!
# Yoruba possession profile
@cite{stassen-2009} @cite{nichols-1986} @cite{heine-1997} 

PossessionProfile bundle for Yoruba (ISO `yor`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativePossession`, `AdnominalPossession`,
…) live in `Linglib/Typology/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Fragments.Yoruba.Possession

open _root_.Typology.Possession

/-- Yoruba possession profile. -/
def possession : PossessionProfile :=
  { language := "Yoruba"
  , family := "Niger-Congo"
  , iso := "yor"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .haveVerb
  , adnominalStrategy := .juxtaposition
  , affixPosition := some .none
  , examples := ["mo ni iwe", "iwe mi"]
  , notes := "Have-verb ni; juxtaposition for adnominal (possessum-possessor)" }

end Fragments.Yoruba.Possession
