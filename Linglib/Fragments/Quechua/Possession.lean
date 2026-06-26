import Linglib.Features.Possession

/-!
# Quechua possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Bare per-language possession `def`s for Quechua (Quechuan, ISO `que`),
per the project's "per-language data flows through Fragments" rule.
Substrate types (`PredicativeStrategy`, `AdnominalMarking`, …) live in
`Linglib/Features/Possession.lean`. Cross-linguistic theorems consuming
these values live in `Studies/NicholsBickel2013.lean`.

Examples: Hwan-pa wasi-n ka-n; mama-y; Hwan-pa wasi-n. Possessive suffixes
obligatory on kinship and body-part nouns; -yuq 'having' for predicative;
GEN + POSS double-marking.
-/

set_option autoImplicit false

namespace Quechua.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .exists_
def possessiveClassification : Classification := .twoWay
def predicativeStrategy : PredicativeStrategy := .haveVerb
def adnominalStrategy : AdnominalMarking := .doubleMarking
def affixPosition : Option AffixPosition := some .noAffix

end Quechua.Possession
