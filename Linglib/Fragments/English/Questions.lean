import Linglib.Syntax.Question

/-!
# English question profile
[wals-2013]

`QuestionProfile` bundle for English (ISO/WALS `eng`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Question.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Dryer2013Question.lean`.

English: no polar Q particle (subject-aux inversion + intonation), wh-fronting
(`what did you see?`), polar formed by interrogative word order
(do-support + inversion).
-/

set_option autoImplicit false

namespace English.Questions

open _root_.Syntax.Question

/-- English question profile. -/
def question : QuestionProfile :=
  { language := "English"
  , walsCode := "eng"
  , qParticlePos := some .noParticle
  , whMovement := some .initial
  , polarStrategy := some .wordOrder }

end English.Questions
