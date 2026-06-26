import Linglib.Features.Possession

/-!
# Yoruba possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Bare per-language possession `def`s for Yoruba (Niger-Congo, ISO `yor`),
per the project's "per-language data flows through Fragments" rule.
Substrate types (`PredicativeStrategy`, `AdnominalMarking`, …) live in
`Linglib/Features/Possession.lean`. Cross-linguistic theorems consuming
these values live in `Studies/NicholsBickel2013.lean`.

Examples: mo ni iwe; iwe mi. Have-verb ni; juxtaposition for adnominal
(possessum-possessor).
-/

set_option autoImplicit false

namespace Yoruba.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .noClassification
def predicativeStrategy : PredicativeStrategy := .haveVerb
def adnominalStrategy : AdnominalMarking := .zeroMarking
def affixPosition : Option AffixPosition := some .noAffix

end Yoruba.Possession
