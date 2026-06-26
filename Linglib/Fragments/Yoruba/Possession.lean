import Linglib.Features.Possession

/-!
# Yoruba possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for Yoruba (ISO `yor`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Yoruba.Possession

open _root_.Possession

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

end Yoruba.Possession
