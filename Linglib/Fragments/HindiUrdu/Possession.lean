import Linglib.Features.Possession

/-!
# Hindiurdu possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for Hindiurdu (ISO `hin`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace HindiUrdu.Possession

open _root_.Possession

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

end HindiUrdu.Possession
