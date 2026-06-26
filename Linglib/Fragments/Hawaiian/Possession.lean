import Linglib.Features.Possession

/-!
# Hawaiian possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Bare per-language possession `def`s for Hawaiian (Austronesian, ISO `haw`),
per the project's "per-language data flows through Fragments" rule.
Substrate types (`PredicativeStrategy`, `AdnominalMarking`, …) live in
`Linglib/Features/Possession.lean`. Cross-linguistic theorems consuming
these values live in `Studies/NicholsBickel2013.lean`.

Examples: ko'u makuahine (o-class); ka'u puke (a-class). Classic Oceanic
alienable vs inalienable: a-class (alienable) vs o-class (inalienable body
parts, kinship, clothing, land).
-/

set_option autoImplicit false

namespace Hawaiian.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .twoWay
def predicativeStrategy : PredicativeStrategy := .locational
def adnominalStrategy : AdnominalMarking := .dependentMarking
def affixPosition : Option AffixPosition := some .noAffix

end Hawaiian.Possession
