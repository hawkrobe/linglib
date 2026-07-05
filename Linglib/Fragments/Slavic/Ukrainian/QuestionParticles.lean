import Linglib.Syntax.Particle.Basic

/-!
# Ukrainian Question Particles
[simik-2024]

Lexical entries for Ukrainian interrogative particles as `Particle`
values. Bias classifications (xiba's evidential requirement) and layer
assignments live in `Simik2024`.

## Cross-Module Connections

- `Simik2024.ukrainian` (`Studies/Simik2024`): PQ strategy profile
  (clause-initial čy obligatory) and the neutral/evidential contrast
- Cross-Slavic RAZVE family: xiba is the Ukrainian cognate of Russian
  razve
-/

namespace Ukrainian.QuestionParticles

/-- чи čy — obligatory clause-initial PQ particle ([simik-2024] ex. 29).
Neutral baseline. -/
def cy : Particle where
  form := "čy"
  script := some "чи"
  position := .clauseInitial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .obligatory
      constituentInterrogative := some .optional }

/-- хіба xiba — mirative/dubitative particle (RAZVE family, [simik-2024]
§4.2.4). Ukrainian cognate of Russian razve: indicates conflict between
speaker's prior state and contextual evidence. Evidential classification
in `Simik2024`. -/
def xiba : Particle where
  form := "xiba"
  script := some "хіба"
  position := .clauseInitial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

def allQuestionParticles : List Particle := [cy, xiba]

end Ukrainian.QuestionParticles
