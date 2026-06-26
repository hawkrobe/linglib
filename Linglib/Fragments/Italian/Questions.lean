import Linglib.Syntax.Question

/-!
# Italian question profile
[wals-2013] [dayal-2025]

`QuestionProfile` bundle for Italian (ISO `ita`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Question.lean`. Cross-linguistic theorems consuming
this profile live in `Studies/Dryer2013Question.lean`. The
forced-clause-typing analysis lives in
`Studies/Dayal2025.lean`.

Italian: no polar Q particle, wh-fronting (not in WALS Ch 93A sample, so
`whMovement = none`), polar formed by intonation only.
-/

set_option autoImplicit false

namespace Italian.Questions

open _root_.Syntax.Question

/-- Italian question profile. -/
def question : QuestionProfile :=
  { language := "Italian"
  , walsCode := "ita"
  , qParticlePos := some .noParticle
  , whMovement := none  -- Italian not in WALS Ch 93A sample
  , polarStrategy := some .intonationOnly }

end Italian.Questions
