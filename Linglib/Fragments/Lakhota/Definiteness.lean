import Linglib.Syntax.Category.Determiner.Basic

/-!
# Lakhota Definiteness Fragment
[schwarz-2013]

Lakhota (Siouan, ISO `lkt`). Two overt definite articles: *kiŋ* (weak,
situational/globally-unique reference) and *k'uŋ* (strong, anaphoric /
'the above-mentioned'). A *bipartite* article system ([schwarz-2013]
§4.2, after Buechel 1939).
-/

namespace Lakhota.Definiteness

/-- Lakhota: weak *kiŋ* (situational uniqueness) and strong *k'uŋ*
    (anaphoric) — two morphologically distinct definite articles. -/
def determiners : List Determiner.Entry :=
  [ .article { form := "kiŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.immediateSituation, .largerSituation] },
    .article { form := "k'uŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric, .donkey] } ]

/-- Lakhota derives the `.bipartite` Moroney cell. -/
theorem marking : Determiner.markingStrategy determiners = .bipartite := by decide

end Lakhota.Definiteness
