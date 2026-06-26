import Linglib.Features.Possession

/-!
# Mandarin possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Per-language possession values for Mandarin (Sino-Tibetan, ISO `cmn`): forms
`wo you yi-ben shu`, `wo de shu`, `wo mama`; have-verb `you`, and `de` marks
adnominal possession but drops with inalienable/close relations. Substrate types
(`PredicativeStrategy`, `AdnominalMarking`, …) live in
`Linglib/Features/Possession.lean`. Cross-linguistic theorems consuming these
values live in `Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Mandarin.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .noClassification
def predicativeStrategy : PredicativeStrategy := .haveVerb
def adnominalStrategy : AdnominalMarking := .dependentMarking
def affixPosition : Option AffixPosition := some .noAffix

end Mandarin.Possession
