import Linglib.Features.Possession

/-!
# Tsotsil possession profile

Per-language possession data for Tsotsil (Mayan; ISO `tzo`) as bare
field-by-field `def`s, following the project's "per-language data flows
through Fragments" rule ([stassen-2009]; [nichols-1986]; [heine-1997];
[aissen-polian-2025]).

## Main declarations

* `obligatoryPossession`, `possessiveClassification`, `predicativeStrategy`,
  `adnominalStrategy`, `affixPosition`: the five possession-profile values.

## Implementation notes

The substrate types (`PredicativeStrategy`, `AdnominalMarking`, …) live in
`Linglib/Features/Possession.lean`; the cross-linguistic theorems consuming
these values live in `Studies/NicholsBickel2013.lean`.

Examples: *oy s-k'ox barko* 'EXIS A3-little.boat', *s-me' Xun* 'A3-mother
Juan' = "Juan's mother", *y-ak'-il li mok=e* 'A3-vine-NCLS DET fence=ENC'.
Existential *oy* + possessive pivot for predicative; Set A prefixes on
possessum for adnominal (head-marking); three noun classes: must/may/cannot
be possessed ([aissen-polian-2025]).
-/

set_option autoImplicit false

namespace Tsotsil.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .exists_
def possessiveClassification : Classification := .threeOrMore
def predicativeStrategy : PredicativeStrategy := .locational
def adnominalStrategy : AdnominalMarking := .headMarking
def affixPosition : Option AffixPosition := some .prefixes

end Tsotsil.Possession
