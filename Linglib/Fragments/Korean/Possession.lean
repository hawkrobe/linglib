import Linglib.Features.Possession

/-!
# Korean possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Per-language possession values for Korean (Koreanic, ISO `kor`): forms
`na-ege chaek-i iss-da`, `Yeonghui-ui chaek`; dative possessor plus existential
`iss-da`, with genitive -ui for adnominal possession. Substrate types
(`PredicativeStrategy`, `AdnominalMarking`, …) live in
`Linglib/Features/Possession.lean`. Cross-linguistic theorems consuming these
values live in `Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Korean.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .noClassification
def predicativeStrategy : PredicativeStrategy := .locational
def adnominalStrategy : AdnominalMarking := .dependentMarking
def affixPosition : Option AffixPosition := Option.none

end Korean.Possession
