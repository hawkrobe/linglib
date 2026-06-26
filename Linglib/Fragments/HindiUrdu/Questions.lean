import Linglib.Syntax.Question

/-!
# Hindi-Urdu question profile
[wals-2013] [bhatt-dayal-2020] [dayal-2025]

`QuestionProfile` bundle for Hindi-Urdu (ISO `hin`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Question.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Dryer2013Question.lean`. The
PerspP analysis of *kya:* lives in
`Studies/BhattDayal2020.lean`; clause-typing typology
in `Studies/Dayal2025.lean`.

Hindi-Urdu: initial polar Q particle *kya:*, wh-in-situ, polar formed by
particle.
-/

set_option autoImplicit false

namespace HindiUrdu.Questions

open _root_.Syntax.Question

/-- Hindi-Urdu question profile. -/
def question : QuestionProfile :=
  { language := "Hindi"
  , walsCode := "hin"
  , qParticlePos := some .initial
  , whMovement := some .inSitu
  , polarStrategy := some .particle }

end HindiUrdu.Questions
