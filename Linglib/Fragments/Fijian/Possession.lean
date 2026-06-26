import Linglib.Features.Possession

/-!
# Fijian possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for Fijian (ISO `fij`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Fijian.Possession

open _root_.Possession

/-- Fijian possession profile. -/
def possession : PossessionProfile :=
  { language := "Fijian"
  , family := "Austronesian"
  , iso := "fij"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .threeOrMore
  , predicativeStrategy := .locational
  , adnominalStrategy := .headMarking
  , affixPosition := some .suffixes
  , examples := ["na liga-qu (body-part)", "na ke-qu kakana (food)", "na me-qu ti (drink)", "na no-qu vale (house)"]
  , notes := "Four-way possessive classification: direct (body/kin), ke- (edible), me- (drinkable), no- (general alienable)" }

end Fijian.Possession
