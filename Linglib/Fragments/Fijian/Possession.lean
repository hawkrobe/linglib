import Linglib.Features.Possession

/-!
# Fijian possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Bare per-language possession `def`s for Fijian (Austronesian, ISO `fij`),
per the project's "per-language data flows through Fragments" rule.
Substrate types (`PredicativeStrategy`, `AdnominalMarking`, …) live in
`Linglib/Features/Possession.lean`. Cross-linguistic theorems consuming
these values live in `Studies/NicholsBickel2013.lean`.

Examples: na liga-qu (body-part); na ke-qu kakana (food); na me-qu ti
(drink); na no-qu vale (house). Four-way possessive classification: direct
(body/kin), ke- (edible), me- (drinkable), no- (general alienable).
-/

set_option autoImplicit false

namespace Fijian.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .threeOrMore
def predicativeStrategy : PredicativeStrategy := .locational
def adnominalStrategy : AdnominalMarking := .headMarking
def affixPosition : Option AffixPosition := some .suffixes

end Fijian.Possession
