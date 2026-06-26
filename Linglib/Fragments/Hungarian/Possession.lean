import Linglib.Features.Possession

/-!
# Hungarian possession profile
[stassen-2009] [nichols-1986] [heine-1997]
[kenesei-vago-fenyvesi-1998] [rounds-2001]

Per-language possession data for Hungarian (Uralic; ISO `hun`), per the
project's "per-language data flows through Fragments" rule, as bare
field-by-field `def`s. Substrate types (`PredicativeStrategy`,
`AdnominalMarking`, …) live in `Linglib/Features/Possession.lean`.
Cross-linguistic theorems consuming these values live in
`Studies/NicholsBickel2013.lean`.

Examples: *nekem van konyvem*, *Janos kalap-ja*. Dative possessor + *van*
'exists' + head-marked possessum; possessive suffixes obligatory on
relational nouns.

The `adnominalStrategy := .headMarking` choice is consistent with both
standard reference grammars: [kenesei-vago-fenyvesi-1998] §1.10
analyzes possession via the possessive suffix on the possessum
(*Péter vers-e* 'Peter's poem' = "Peter poem-POSS"), with the optional
*dative* possessor (*Péter-nek a vers-e* "Peter-DAT the poem-POSS")
when extracted for specificity reasons (per Szabolcsi 1986/1992, 1994,
as cited there). Both KVF and [rounds-2001] treat the
possessor-marker as **dative**, not genitive — Hungarian has no
morphological GEN, and `Fragments/Hungarian/Case.lean` reflects this
by omitting `.gen` from its `caseInventory`.
-/

set_option autoImplicit false

namespace Hungarian.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .exists_
def possessiveClassification : Classification := .noClassification
def predicativeStrategy : PredicativeStrategy := .locational
def adnominalStrategy : AdnominalMarking := .headMarking
def affixPosition : Option AffixPosition := some .suffixes

end Hungarian.Possession
