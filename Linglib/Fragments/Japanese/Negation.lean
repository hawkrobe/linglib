import Linglib.Morphology.Morphotactics.RelevanceHierarchy
import Linglib.Syntax.Negation

/-!
# Japanese negation

Japanese negates a plain verb with the suffix *-na-* on its stem, and the negative inflects as
an adjective: *tabe-ru* 'eats' has the negative *tabe-na-i* and *tabe-ta* 'ate' the negative
*tabe-na-katta*, with the adjectival endings *-i* and *-katta*, not the verbal *-ru* and *-ta*.
In the polite style the negative *-en* stands in place of the nonpast ending, *tabe-mas-u* and
*tabe-mas-en*, and the past negative adds the past of the polite copula, *tabe-mas-en deshita*
beside *tabe-mashi-ta*, where *-mashi-* is the form of *-mas-* before *-ta*.
Tense thus leaves the verb under negation, while each affirmative form keeps its own negative.
The examples are those of [miestamo-2005], from Hinds's grammar.

## Main definitions

* `Japanese.Negation.na`, `Japanese.Negation.en`: the plain and the polite negative suffix
* `Japanese.Negation.plain`, `Japanese.Negation.polite`: the nonpast and past of *tabe-* 'eat'
  with their negatives
* `Japanese.Negation.japaneseNegDistribution`: the categories marked on the stem and on the
  suffix in the affirmative and the negative

## References

* [miestamo-2005]
-/

namespace Japanese.Negation

open Morphology (MorphCategory)
open Syntax.Negation

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

/-- Where the inflectional categories are marked: on the stem in the affirmative, and in the
negative on the negative suffix. -/
structure NegInflDistribution where
  /-- The categories on the verb stem in the affirmative. -/
  affirmativeOnStem : Finset MorphCategory
  /-- The categories on the verb stem in the negative. -/
  negativeOnStem : Finset MorphCategory
  /-- The categories on the negative suffix. -/
  negativeOnSuffix : Finset MorphCategory
  deriving DecidableEq

/-- Tense, mood and agreement leave the stem for the suffix under negation. -/
def japaneseNegDistribution : NegInflDistribution :=
  { affirmativeOnStem := {.tense, .aspect, .mood, .agreement .subj},
    negativeOnStem := {.aspect},
    negativeOnSuffix := {.negation, .tense, .mood} }

end Japanese.Negation
