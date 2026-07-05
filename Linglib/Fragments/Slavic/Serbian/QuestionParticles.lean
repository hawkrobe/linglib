import Linglib.Syntax.Particle.Basic

/-!
# Serbian Question Particles
[simik-2024]

Lexical entries for Serbian interrogative particles as `Particle` values.
Bias classifications (zar's evidential requirement) and layer assignments
live in `Simik2024`.

## Cross-Module Connections

- `Simik2024.serbian` (`Studies/Simik2024`): PQ strategy profile
  (da li + verb movement) and the neutral/evidential contrast
-/

namespace Serbian.QuestionParticles

/-- da li — default PQ particle combination ([simik-2024] ex. 31):
clause-initial particle + verb movement. Neutral baseline. -/
def daLi : Particle where
  form := "da li"
  position := some .clauseInitial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

/-- zar — mirative/dubitative particle (RAZVE family, [simik-2024]
§4.2.4). Compatible with both outer and inner negation (like Russian
razve). Evidential classification in `Simik2024`. -/
def zar_ : Particle where
  form := "zar"
  position := some .clauseInitial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

def allQuestionParticles : List Particle := [daLi, zar_]

end Serbian.QuestionParticles
