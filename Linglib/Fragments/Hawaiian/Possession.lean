import Linglib.Typology.Possession

/-!
# Hawaiian possession profile
@cite{stassen-2009} @cite{nichols-1986} @cite{heine-1997} 

PossessionProfile bundle for Hawaiian (ISO `haw`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativePossession`, `AdnominalPossession`,
…) live in `Linglib/Typology/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Phenomena/Possession/Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Fragments.Hawaiian.Possession

open _root_.Typology.Possession

/-- Hawaiian possession profile. -/
def possession : PossessionProfile :=
  { language := "Hawaiian"
  , family := "Austronesian"
  , iso := "haw"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .twoWay
  , predicativeStrategy := .locational
  , adnominalStrategy := .dependentMarking
  , affixPosition := some .none
  , examples := ["ko'u makuahine (o-class)", "ka'u puke (a-class)"]
  , notes := "Classic Oceanic alienable/inalienable: a-class (alienable) vs o-class (inalienable body parts, kinship, clothing, land)" }

end Fragments.Hawaiian.Possession
