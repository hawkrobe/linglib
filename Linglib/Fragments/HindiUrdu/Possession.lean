import Linglib.Features.Possession

/-!
# Hindiurdu possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Per-language possession values for Hindi-Urdu (Indo-European, ISO `hin`): forms
`mere paas kitaab hai`, `Raam kaa ghar`; postposition `paas` 'near' for
predicative possession, and the agreeing genitive postposition kaa ~ ke ~ kii
for adnominal possession. Substrate types (`PredicativeStrategy`,
`AdnominalMarking`, …) live in `Linglib/Features/Possession.lean`.
Cross-linguistic theorems consuming these values live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace HindiUrdu.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .noClassification
def predicativeStrategy : PredicativeStrategy := .locational
def adnominalStrategy : AdnominalMarking := .dependentMarking
def affixPosition : Option AffixPosition := Option.none

end HindiUrdu.Possession
