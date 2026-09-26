module

public import Linglib.Syntax.Case.Basic

/-!
# Tamil case

Tamil has eight cases, the seven of Classical Armenian on Blake's inflectional case hierarchy,
the nominative, accusative, genitive, dative, locative, ablative and instrumental, and the
comitative, which Dravidian grammars call the sociative. The oblique cases of some singular
nouns are suffixed to an oblique stem distinct from the nominative: *maram* 'tree' has the
accusative *maratt-ai* and the dative *maratt-ukku*, and the stem-forming element never
appears without a following case suffix, so that the nominative stands off from the other
cases. Blake takes Tamil as the eight-case stage of his hierarchy (`Studies/Blake1994.lean`).

## Main definitions

* `Tamil.Case.inventory`: the eight cases.

## References

* [blake-1994]
-/

@[expose] public section

namespace Tamil.Case

/-- The eight cases. -/
def inventory : Finset Case := {.nom, .acc, .gen, .dat, .loc, .abl, .inst, .com}

end Tamil.Case
