import Linglib.Typology.Possession

/-!
# Tsotsil possession profile
@cite{stassen-2009} @cite{nichols-1986} @cite{heine-1997} @cite{aissen-polian-2025}

PossessionProfile bundle for Tsotsil (ISO `tzo`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativePossession`, `AdnominalPossession`,
…) live in `Linglib/Typology/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Fragments.Mayan.Tsotsil.Possession

open _root_.Typology.Possession

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

end Fragments.Mayan.Tsotsil.Possession
