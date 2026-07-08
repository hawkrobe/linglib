import Linglib.Syntax.Category.Particle.Basic

/-!
# Russian Question Particles
[esipova-romero-2023] [simik-2024]

Lexical entries for Russian interrogative particles as `Particle`
values. Bias classifications (razve's evidential requirement) and layer
assignments live in `Simik2024`.

## Cross-Module Connections

- `Simik2024.russian` (`Studies/Simik2024`): PQ strategy profile
  (intonation default, li formal) and the neutral/evidential contrast
-/

namespace Russian.QuestionParticles

/-- ли li — neutral polar question particle (formal register).
Second-position (Wackernagel) enclitic, cliticizes onto the focused
constituent. Rare in spoken Russian (only 6/500 PQs in Onoeva &
Staňková corpus). -/
def li : Particle where
  form := "li"
  script := some "ли"
  position := some .secondPosition
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

/-- разве razve — mirative/dubitative question particle ([simik-2024]
§4.2.4). Indicates conflict between speaker's prior epistemic state and
current contextual evidence. Compatible with both outer and inner
negation. Evidential classification in `Simik2024`. -/
def razve_ : Particle where
  form := "razve"
  script := some "разве"
  position := some .clauseInitial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

def allQuestionParticles : List Particle := [li, razve_]

end Russian.QuestionParticles
