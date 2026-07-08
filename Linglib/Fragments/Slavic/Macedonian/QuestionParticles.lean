import Linglib.Syntax.Category.Particle.Basic

/-!
# Macedonian Question Particles
[simik-2024]

Lexical entry for Macedonian *dali* as a `Particle` value. Macedonian
*dali* can introduce negative PQs without triggering epistemic bias,
unlike Bulgarian *li* ([simik-2024] ex. 32) — that contrast is an
analytical classification and lives in `Simik2024`. Mitkovska,
Bužarovska & Saračević (2024) contrast *dali* with biased particles
*zar* and *neli*.

## Cross-Module Connections

- `Simik2024.macedonian` (`Studies/Simik2024`): PQ strategy profile
  (negation does not trigger bias)
-/

namespace Macedonian.QuestionParticles

/-- дали dali — clause-initial PQ particle ([simik-2024] ex. 32). -/
def dali : Particle where
  form := "dali"
  script := some "дали"
  position := some .clauseInitial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

def allQuestionParticles : List Particle := [dali]

end Macedonian.QuestionParticles
