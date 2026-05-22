import Linglib.Typology.Possession

/-!
# Hindiurdu possession profile
@cite{stassen-2009} @cite{nichols-1986} @cite{heine-1997} 

PossessionProfile bundle for Hindiurdu (ISO `hin`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativePossession`, `AdnominalPossession`,
…) live in `Linglib/Typology/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Fragments.HindiUrdu.Possession

open _root_.Typology.Possession

/-- Hindiurdu possession profile. -/
def possession : PossessionProfile :=
  { language := "Hindiurdu"
  , family := "Indo-European"
  , iso := "hin"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .genitiveDative
  , adnominalStrategy := .dependentMarking
  , affixPosition := Option.none
  , examples := ["mere paas kitaab hai", "Raam kaa ghar"]
  , notes := "Postposition paas 'near' for predicative; kaa/ke/kii agreeing genitive postposition for adnominal" }

end Fragments.HindiUrdu.Possession
