import Linglib.Syntax.Particle.Basic

/-!
# Slovenian Question Particles
[simik-2024]

Lexical entry for Slovenian *ali* as a `Particle` value. Layer
assignment lives in `Simik2024`.

## Cross-Module Connections

- `Simik2024.slovenian` (`Studies/Simik2024`): PQ strategy profile
-/

namespace Slovenian.QuestionParticles

/-- ali — clause-initial PQ particle ([simik-2024] ex. 28). Optional in
default PQs; incompatible with DeclPQs. -/
def ali : Particle where
  form := "ali"
  position := .clauseInitial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

def allQuestionParticles : List Particle := [ali]

end Slovenian.QuestionParticles
