import Linglib.Syntax.Question

/-!
# Japanese question profile
[wals-2013] [bhatt-dayal-2020] [sauerland-yatsushiro-2017]

`QuestionProfile` bundle for Japanese (ISO `jpn`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Question.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Dryer2013Question.lean`. The
CP-layer *ka* and SAP-layer *kke* analyses live in
`Studies/BhattDayal2020.lean`.

Japanese: final polar Q particle *ka*, wh-in-situ, polar formed by particle.
-/

set_option autoImplicit false

namespace Japanese.Questions

open _root_.Syntax.Question

/-- Japanese question profile. -/
def question : QuestionProfile :=
  { language := "Japanese"
  , walsCode := "jpn"
  , qParticlePos := some .final
  , whMovement := some .inSitu
  , polarStrategy := some .particle }

end Japanese.Questions
