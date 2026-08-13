import Linglib.Syntax.Category.Determiner.Basic

/-!
# German determiner inventory

German morphologically distinguishes two definite articles: the weak article,
usually contracted (*im*, *vom*, *zum*), marks situational uniqueness, and
the strong full form (*dem*, *von dem*) marks anaphoric reference, including
covarying (donkey) uses. Indefinite *ein-*, demonstrative *dieser*, and
possessives complete the inventory.

## References

* [schwarz-2009]
* [schwarz-2013], §3
* [moroney-2021]
-/

namespace German.Determiners

/-- The German determiners are the weak definite (contracted, *im*), the
    strong definite (*dem*), the indefinite *ein-*, the demonstrative
    *dieser*, and the possessives. -/
def inventory : Determiner.Inventory :=
  [ .article { form := "im/weak", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.immediateSituation, .largerSituation] },
    .article { form := "dem/strong", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric, .donkey] },
    .article { form := "ein", definiteness := .indefinite, exponent := .dedicatedMorpheme },
    .demonstrative { form := "dieser", deictic := .unspecified },
    .possessive { form := "mein" } ]

/-- German derives the `.bipartite` Moroney cell. -/
theorem marking : inventory.markingStrategy = .bipartite := by decide

end German.Determiners
