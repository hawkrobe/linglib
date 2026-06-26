import Linglib.Features.Possession

/-!
# Hawaiian possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for Hawaiian (ISO `haw`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Hawaiian.Possession

open _root_.Possession

/-- Hawaiian possession profile. -/
def possession : PossessionProfile :=
  { language := "Hawaiian"
  , family := "Austronesian"
  , iso := "haw"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .twoWay
  , predicativeStrategy := .locational
  , adnominalStrategy := .dependentMarking
  , affixPosition := some .noAffix
  , examples := ["ko'u makuahine (o-class)", "ka'u puke (a-class)"]
  , notes := "Classic Oceanic alienable/inalienable: a-class (alienable) vs o-class (inalienable body parts, kinship, clothing, land)" }

end Hawaiian.Possession
