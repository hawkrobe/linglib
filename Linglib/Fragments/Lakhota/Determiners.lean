import Linglib.Syntax.Category.Determiner.Basic

/-!
# Lakhota determiner inventory

Lakhota (Siouan, ISO `lkt`) has two overt definite articles: *kiŋ*, used for
situationally and globally unique referents, and *k'uŋ*, glossed 'the
above-mentioned' and treated as an anaphoric article in most of the
literature. The classification is tentative: [ingham-2003] reports an
anaphoric use of *kiŋ*, rival accounts analyze *k'uŋ* in terms of
accessibility or switch reference, and covarying (donkey) uses are
unreported for either article.

## References

* [schwarz-2013], §4.2.1
* [ingham-2003]
-/

namespace Lakhota.Determiners

/-- The Lakhota determiners are the weak definite *kiŋ* and the strong
    definite *k'uŋ*. -/
def inventory : Determiner.Inventory :=
  [ .article { form := "kiŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.immediateSituation, .largerSituation] },
    .article { form := "k'uŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric] } ]

/-- Lakhota derives the `.bipartite` Moroney cell. -/
theorem marking : inventory.markingStrategy = .bipartite := by decide

end Lakhota.Determiners
