import Linglib.Syntax.Category.Determiner.Basic

/-!
# Fering Definiteness Fragment
[schwarz-2013]

Fering (North Frisian, ISO `frr`). Ebert's **A-form** (weak article,
situational uniqueness) contrasts with the **D-form** (strong article,
anaphoric/familiarity) — a *bipartite* article system, one of
[schwarz-2013]'s two clearest weak/strong languages (§3).
-/

namespace Fering.Definiteness

/-- Fering: weak A-form *a/at* (uniqueness) and strong D-form *di/det*
    (anaphoric) — two morphologically distinct definite articles. -/
def determiners : List Determiner.Entry :=
  [ .article { form := "a", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.immediateSituation, .largerSituation] },
    .article { form := "di", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric, .donkey] } ]

/-- Fering derives the `.bipartite` Moroney cell. -/
theorem marking : Determiner.markingStrategy determiners = .bipartite := by decide

end Fering.Definiteness
