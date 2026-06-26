import Linglib.Features.Possession

/-!
# Tsotsil possession profile
[stassen-2009] [nichols-1986] [heine-1997] [aissen-polian-2025]

PossessionProfile bundle for Tsotsil (ISO `tzo`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Tsotsil.Possession

open _root_.Possession

/-- Tsotsil possession profile. -/
def possession : PossessionProfile :=
  { language := "Tsotsil"
  , family := "Mayan"
  , iso := "tzo"
  , obligatoryPossession := .exists_
  , possessiveClassification := .threeOrMore
  , predicativeStrategy := .locational
  , adnominalStrategy := .headMarking
  , affixPosition := some .prefixes
  , examples := ["oy s-k'ox barko 'EXIS A3-little.boat'", "s-me' Xun 'A3-mother Juan' = 'Juan's mother'", "y-ak'-il li mok=e 'A3-vine-NCLS DET fence=ENC'"]
  , notes := "Existential oy + possessive pivot for predicative; Set A prefixes on possessum for adnominal (head-marking); three noun classes: must/may/cannot be possessed (Aissen-Polian 2025)" }

end Tsotsil.Possession
