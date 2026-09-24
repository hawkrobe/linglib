module

public import Linglib.Syntax.Case.Basic

/-!
# Turkish case

This file defines the cases of Turkish. Göksel and Kerslake list five case suffixes, the
accusative *-(y)I*, the dative *-(y)A*, the locative *-DA*, the ablative *-DAn* and the genitive
*-(n)In*, and Blake's table adds the unmarked nominative for a system of six cases. The
suffixes are the case exponents of the nominal in `Morphotactics.lean`, which maps each to its
label here and proves that the inventory is the nominative with the cases they realize. The
comitative and instrumental *-(y)lA* is not a case suffix in the grammar's analysis but an
unstressable marker that forms postpositional phrases.

## Main definitions

* `Turkish.Case.inventory`: the six cases

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [B. J. Blake, *Case* (1994)][blake-1994]
-/

@[expose] public section

namespace Turkish.Case

/-- The six cases. -/
def inventory : Finset Case := {.nom, .acc, .dat, .loc, .abl, .gen}

end Turkish.Case
