module

public import Linglib.Syntax.Case.Basic

/-!
# Hungarian case

Hungarian marks case by agglutinative suffix. Kenesei, Vago and Fenyvesi list eighteen cases:
the nominative, the accusative *-t*, the dative *-nak ~ -nek*, the instrumental *-val ~ -vel*,
the causal *-ért*, the essive *-ul ~ -ül*, the essive-formal *-ként*, the terminative *-ig*, the
translative *-vá ~ -vé*, and the nine local cases, which form a matrix of three regions,
interior, exterior and near, by three directions, motion toward, rest and motion away: the
illative *-ba ~ -be*, inessive *-ban ~ -ben* and elative *-ból ~ -ből*, the sublative *-ra ~
-re*, superessive *-n* and delative *-ról ~ -ről*, and the allative *-hoz*, adessive *-nál ~
-nél* and ablative *-tól ~ -től*. Rounds adds the less productive temporal *-kor*, distributive
*-nként*, distributive-temporal *-nta* and sociative *-stul ~ -stül*. There is no genitive: the
possessor within the noun phrase is nominative or dative, and both grammars gloss *-nak ~ -nek*
as a dative throughout, the reading under which Blake and Caha take Hungarian's missing
genitive as a superficial exception to the case hierarchy.

## Main definitions

* `Hungarian.Case.inventory`: the cases the comparative labels cover.

## Implementation notes

The essive-formal, the distributive, the distributive-temporal and the sociative have no
comparative label and are not in the inventory; the instrumental *-val ~ -vel* also expresses
accompaniment, and no separate comitative is recorded.

## References

* [kenesei-vago-fenyvesi-1998]
* [rounds-2001]
* [caha-2008]
-/

@[expose] public section

namespace Hungarian.Case

/-- The cases under their comparative labels are the three grammatical cases, the nine local
cases, the instrumental, the causal, the essive, the translative, the terminative and the
temporal. -/
def inventory : Finset Case :=
  {.nom, .acc, .dat, .ine, .ade, .sup, .ela, .abl, .del, .ill, .all, .sub, .inst, .caus, .ess,
    .transl, .ter, .tem}

end Hungarian.Case
