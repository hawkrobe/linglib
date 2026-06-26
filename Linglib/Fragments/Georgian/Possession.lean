import Linglib.Features.Possession

/-!
# Georgian possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Bare per-language possession `def`s for Georgian (Kartvelian, ISO `kat`),
per the project's "per-language data flows through Fragments" rule.
Substrate types (`PredicativeStrategy`, `AdnominalMarking`, …) live in
`Linglib/Features/Possession.lean`. Cross-linguistic theorems consuming
these values live in `Studies/NicholsBickel2013.lean`.

Examples: me m-akvs cigni; kac-is saxl-i. Dative experiencer + verb
agreeing with possessum; genitive on possessor in adnominal constructions.
-/

set_option autoImplicit false

namespace Georgian.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .noClassification
def predicativeStrategy : PredicativeStrategy := .locational
def adnominalStrategy : AdnominalMarking := .doubleMarking
def affixPosition : Option AffixPosition := some .noAffix

end Georgian.Possession
