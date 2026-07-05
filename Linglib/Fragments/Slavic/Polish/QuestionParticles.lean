import Linglib.Syntax.Particle.Basic

/-!
# Polish Question Particles
[simik-2024]

Lexical entries for Polish interrogative particles as `Particle` values.
Bias classifications (czyżby's evidential requirement) and layer
assignments live in `Simik2024`.

## Cross-Module Connections

- `Simik2024.polish` (`Studies/Simik2024`): PQ strategy profile
  (clause-initial czy obligatory) and the neutral/evidential contrast
- Cross-Slavic RAZVE family: czyżby is the Polish member
-/

namespace Polish.QuestionParticles

/-- czy — obligatory clause-initial PQ particle ([simik-2024] ex. 30).
Verb-initial PQs possible but unacceptable in quiz scenarios. -/
def czy : Particle where
  form := "czy"
  position := .clauseInitial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .obligatory
      constituentInterrogative := some .optional }

/-- czyżby — mirative/dubitative particle (RAZVE family, [simik-2024]
§4.2.4). Polish member of the cross-Slavic razve family. Evidential
classification in `Simik2024`. -/
def czyzby : Particle where
  form := "czyżby"
  position := .clauseInitial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

def allQuestionParticles : List Particle := [czy, czyzby]

end Polish.QuestionParticles
