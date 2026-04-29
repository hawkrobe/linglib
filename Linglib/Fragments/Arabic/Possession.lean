import Linglib.Typology.Possession

/-!
# Arabic possession profile
@cite{stassen-2009} @cite{nichols-1986} @cite{heine-1997} 

PossessionProfile bundle for Arabic (ISO `arb`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativePossession`, `AdnominalPossession`,
…) live in `Linglib/Typology/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Phenomena/Possession/Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Fragments.Arabic.Possession

open _root_.Typology.Possession

/-- Arabic possession profile. -/
def possession : PossessionProfile :=
  { language := "Arabic"
  , family := "Afro-Asiatic"
  , iso := "arb"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .genitiveDative
  , adnominalStrategy := .juxtaposition
  , affixPosition := some .suffixes
  , examples := ["indi kitaab", "kitaabu l-waladi"]
  , notes := "Preposition inda for predicative; construct state (idaafa) for adnominal -- juxtaposition with reduced head vowel" }

end Fragments.Arabic.Possession
