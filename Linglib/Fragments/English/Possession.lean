import Linglib.Features.Possession

/-!
# English possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Per-language possession values for English (Indo-European, ISO `eng`): forms
`I have a book`, `John's book`, `the book of John`; genitive clitic -'s on the
possessor, with an of-phrase alternative. Substrate types (`PredicativeStrategy`,
`AdnominalMarking`, …) live in `Linglib/Features/Possession.lean`.
Cross-linguistic theorems consuming these values live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace English.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .noClassification
def predicativeStrategy : PredicativeStrategy := .haveVerb
def adnominalStrategy : AdnominalMarking := .dependentMarking
def affixPosition : Option AffixPosition := some .noAffix

end English.Possession
