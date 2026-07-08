import Linglib.Syntax.Category.Determiner.Basic

/-!
# Hausa Definiteness Fragment
[schwarz-2013]

Hausa (Chadic, ISO `ha`). Two definite forms differentiating two types of
definiteness: a weak suffixal *-n* (situational uniqueness) and a strong *ɗîn*
(anaphoric) — a *bipartite* article system ([schwarz-2013] §4.2).
-/

namespace Hausa

/-- Hausa: weak suffixal *-n* (uniqueness) and strong *ɗîn* (anaphoric) —
    two morphologically distinct definite forms. -/
def determiners : List Determiner.Entry :=
  [ .article { form := "-n", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.immediateSituation, .largerSituation] },
    .article { form := "ɗîn", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric, .donkey] } ]

/-- Hausa derives the `.bipartite` Moroney cell. -/
theorem marking : Determiner.markingStrategy determiners = .bipartite := by decide

end Hausa
