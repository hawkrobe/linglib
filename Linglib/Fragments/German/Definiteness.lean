import Linglib.Syntax.Category.Determiner.Basic

/-!
# German Definiteness Fragment
[schwarz-2009] [schwarz-2013] [moroney-2021]

German morphologically distinguishes the weak (uniqueness) article — often
contracted, e.g., *im*, *vom*, *zum* — from the strong (anaphoric/familiarity)
article — full forms *dem*, *von dem*. Indefinite *ein-*, demonstratives,
and possessives complete the inventory. Under the [moroney-2021]
typology this is the `.bipartite` strategy: distinct forms for each
[schwarz-2009] use type.
-/

namespace German.Definiteness

/-- German: *distinct* weak (uniqueness, e.g. contracted *im*) and strong
    (anaphoric, *dem*) definite articles; indefinite *ein-*; demonstratives;
    possessives. The unique vs anaphoric distinction is morphologically marked. -/
def determiners : List Determiner.Entry :=
  [ .article { form := "im/weak", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.immediateSituation, .largerSituation] },
    .article { form := "dem/strong", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric, .donkey] },
    .article { form := "ein", definiteness := .indefinite, exponent := .dedicatedMorpheme },
    .demonstrative { form := "dieser", deictic := .unspecified },
    .possessive { form := "mein" } ]

/-- German's inventory derives the `.bipartite` Moroney cell. -/
theorem marking : Determiner.markingStrategy determiners = .bipartite := by decide

end German.Definiteness
