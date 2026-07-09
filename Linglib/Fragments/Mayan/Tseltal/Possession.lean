import Linglib.Features.Possession

/-!
# Tseltal possession profile

Per-language possession data for Tseltal (Mayan; ISO `tzh`) as bare
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

Examples: *ay chenek' ta oxom* 'EXIS bean P pot', *s-be-lal te j-na=e*
'A3-road-NCLS DET A1-house=ENC'. Existential *ay* + possessive pivot for
predicative; Set A prefixes on possessum for adnominal (head-marking); three
noun classes as in Tsotsil ([aissen-polian-2025]).
-/

set_option autoImplicit false

namespace Tseltal.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .exists_
def possessiveClassification : Classification := .threeOrMore
def predicativeStrategy : PredicativeStrategy := .locational
def adnominalStrategy : AdnominalMarking := .headMarking
def affixPosition : Option AffixPosition := some .prefixes

end Tseltal.Possession
