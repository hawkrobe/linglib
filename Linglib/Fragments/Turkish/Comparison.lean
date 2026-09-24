module

public import Linglib.Syntax.Comparative

/-!
# Turkish comparison

This file defines the Turkish comparative construction as Göksel and Kerslake describe it. The
standard of comparison takes the ablative and the adjective is preceded by the adverb *daha*
'more', which may be omitted when the ablative complement is present, *bu makine öbüründen
(daha) ucuz* 'this machine is cheaper than the other one'; the superlative is the adverb *en*
'most' before the adjective. The construction's type, read off its anatomy, is locational.

## Main definitions

* `Turkish.Comparison.dan`: the comparative construction
* `Turkish.Comparison.degreeWord`: the free degree word *daha*

## Main results

* `Turkish.Comparison.type_dan`: the construction is locational

## Implementation notes

* The superlative *en* is a free adverb that `SuperlativeStrategy` has no case for, so none is
  recorded.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

@[expose] public section

namespace Turkish.Comparison

open Comparative

/-- The ablative comparative, whose standard takes *-DAn* and whose adjective is preceded by
the optional *daha* and carries no comparative morphology. -/
def dan : Comparative :=
  { standardMarker := some "-DAn", caseAssignment := .fixed, fixedEncoding := some .adverbial,
    standardCase := some .abl, degreeMarker := some "daha" }

/-- The degree word *daha* is free and optional. -/
def degreeWord : DegreeWordType := .hasDegreeWord

/-- The construction is locational. -/
theorem type_dan : dan.type = .locational := rfl

end Turkish.Comparison
