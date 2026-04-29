import Linglib.Typology.Question

/-!
# Japanese question profile
@cite{wals-2013} @cite{bhatt-dayal-2020} @cite{sauerland-yatsushiro-2017}

`QuestionProfile` bundle for Japanese (ISO `jpn`) per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Question.lean`. Cross-linguistic theorems consuming
this profile live in `Phenomena/Questions/Studies/Dryer2013.lean`. The
CP-layer *ka* and SAP-layer *kke* analyses live in
`Phenomena/Questions/Studies/BhattDayal2020.lean`.

Japanese: final polar Q particle *ka*, wh-in-situ, polar formed by particle.
-/

set_option autoImplicit false

namespace Fragments.Japanese.Questions

open _root_.Typology.Question

/-- Japanese question profile. -/
def question : QuestionProfile :=
  { language := "Japanese"
  , walsCode := "jpn"
  , qParticlePos := some .final
  , whMovement := some .inSitu
  , polarStrategy := some .particle }

end Fragments.Japanese.Questions
