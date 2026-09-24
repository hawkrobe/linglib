module

public import Linglib.Syntax.Comparative

/-!
# Japanese comparison

Japanese marks the standard of comparison with the postposition *yori* 'than' and leaves the
predicate without degree marking: *Taroo-wa Hanako-yori zutto haya-ku ki-ta* 'Taro came a lot
earlier than Hanako'. The standard's case is fixed by the construction, the ablative the case
fragment records for *yori* (`Japanese.Case.yori`), which `Studies/Stassen1985.lean` reads as
Stassen's separative type. The superlative is formed with the adverb *itiban*
'most', *itiban haya-ku* 'the fastest', which none of `SuperlativeStrategy`'s cases fits.

## References

* [tsujimura-2014]
* [stassen-1985]
-/

@[expose] public section

namespace Japanese.Comparison

open Comparative

/-- The *yori*-comparative: the standard marked by the postposition *yori* in the ablative, and no
degree morphology. -/
def yori : Comparative :=
  { standardMarker := some "yori"
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardCase := some .abl }

end Japanese.Comparison
