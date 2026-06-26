import Linglib.Features.Possession

/-!
# Japanese possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Per-language possession values for Japanese (Japonic, ISO `jpn`): forms
`watashi-ni-wa hon-ga aru`, `Tanaka-no hon`; topic-comment predication
(possessor-DAT-TOP possessum-NOM aru/iru) with genitive `no` for adnominal
possession. Substrate types (`PredicativeStrategy`, `AdnominalMarking`, …) live
in `Linglib/Features/Possession.lean`. Cross-linguistic theorems consuming these
values live in `Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Japanese.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .noClassification
def predicativeStrategy : PredicativeStrategy := .topic
def adnominalStrategy : AdnominalMarking := .dependentMarking
def affixPosition : Option AffixPosition := some .noAffix

end Japanese.Possession
