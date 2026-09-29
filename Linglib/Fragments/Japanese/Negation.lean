module

public import Linglib.Syntax.Negation

/-!
# Japanese negation

Japanese negates a plain verb with the suffix *-na-* on its stem, and the negative inflects as
an adjective: *tabe-ru* 'eats' has the negative *tabe-na-i* and *tabe-ta* 'ate' the negative
*tabe-na-katta*, with the adjectival endings *-i* and *-katta*, not the verbal *-ru* and *-ta*.
In the polite style the negative *-en* stands in place of the nonpast ending, *tabe-mas-u* and
*tabe-mas-en*, and the past negative adds the past of the polite copula, *tabe-mas-en deshita*
beside *tabe-mashi-ta*, where *-mashi-* is the form of *-mas-* before *-ta*.
A plain verb thus becomes an adjective under negation, the adjectival tense endings replacing
the verbal ones, while each affirmative form keeps its own negative. The examples are those of
[miestamo-2005], from Hinds's grammar.

## Main definitions

* `Japanese.Negation.na`, `Japanese.Negation.en`: the plain and the polite negative suffix
* `Japanese.Negation.plain`, `Japanese.Negation.polite`: the nonpast and past of *tabe-* 'eat'
  with their negatives
* `Japanese.Negation.adjectivalEndings`: the adjectival tense endings

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation

namespace Japanese.Negation

open Morphology (Morph)

/-- The plain negative suffix *-na-*, inflected as an adjective. -/
def na : Marker := { pieces := [[.suff "na"]] }

/-- The polite negative suffix *-en*. -/
def en : Marker := { pieces := [[.suff "en"]] }

/-- The plain nonpast and past of *tabe-* 'eat'. -/
def plain : List Pair :=
  [⟨[.root "tabe", .suff "ru"], [.root "tabe", .suff "na", .suff "i"]⟩,
   ⟨[.root "tabe", .suff "ta"], [.root "tabe", .suff "na", .suff "katta"]⟩]

/-- The polite nonpast and past of *tabe-* 'eat'. -/
def polite : List Pair :=
  [⟨[.root "tabe", .suff "mas", .suff "u"], [.root "tabe", .suff "mas", .suff "en"]⟩,
   ⟨[.root "tabe", .suff "mas", .suff "ta"],
    [.root "tabe", .suff "mas", .suff "en", .free "deshita"]⟩]

/-- The adjectival tense endings, the non-past *-i* and the past *-katta*. -/
def adjectivalEndings : List Morph := [.suff "i", .suff "katta"]

end Japanese.Negation
