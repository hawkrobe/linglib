import Linglib.Features.Possession

/-!
# Tseltal possession profile
[stassen-2009] [nichols-1986] [heine-1997] [aissen-polian-2025]

PossessionProfile bundle for Tseltal (ISO `tzh`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Tseltal.Possession

open _root_.Possession

/-- Tseltal possession profile. -/
def possession : PossessionProfile :=
  { language := "Tseltal"
  , family := "Mayan"
  , iso := "tzh"
  , obligatoryPossession := .exists_
  , possessiveClassification := .threeOrMore
  , predicativeStrategy := .locational
  , adnominalStrategy := .headMarking
  , affixPosition := some .prefixes
  , examples := ["ay chenek' ta oxom 'EXIS bean P pot'", "s-be-lal te j-na=e 'A3-road-NCLS DET A1-house=ENC'"]
  , notes := "Existential ay + possessive pivot for predicative; Set A prefixes on possessum for adnominal (head-marking); three noun classes as in Tsotsil (Aissen-Polian 2025)" }

end Tseltal.Possession
