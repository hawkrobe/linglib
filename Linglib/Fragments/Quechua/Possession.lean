import Linglib.Features.Possession

/-!
# Quechua possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for Quechua (ISO `que`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Quechua.Possession

open _root_.Possession

/-- Quechua possession profile. -/
def possession : PossessionProfile :=
  { language := "Quechua"
  , family := "Quechuan"
  , iso := "que"
  , obligatoryPossession := .exists_
  , possessiveClassification := .twoWay
  , predicativeStrategy := .haveVerb
  , adnominalStrategy := .doubleMarking
  , affixPosition := some .noAffix
  , examples := ["Hwan-pa wasi-n ka-n", "mama-y", "Hwan-pa wasi-n"]
  , notes := "Possessive suffixes obligatory on kinship/body-part nouns; -yuq 'having' for predicative; GEN + POSS double-marking" }

end Quechua.Possession
