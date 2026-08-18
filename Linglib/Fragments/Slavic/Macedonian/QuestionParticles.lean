import Linglib.Syntax.Category.Particle.Basic

/-!
# Macedonian question particles
[simik-2024]

Macedonian default polar questions are introduced by clause-initial
*dali*, which admits negation without inducing bias ([simik-2024]
ex. 32); the mirative *zar* of the cross-Slavic RAZVE family conveys
strong bias and is excluded from neutral questions ([simik-2024] §4.1,
§4.2.4).
-/

namespace Macedonian.QuestionParticles

/-- дали dali is the clause-initial polar question particle. -/
def dali : Particle where
  form := "dali"
  script := some "дали"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | .constituent, .matrix => some .excluded
    | _, _ => none

/-- зар zar is a mirative/dubitative particle of the cross-Slavic RAZVE
family. -/
def zar : Particle where
  form := "zar"
  script := some "зар"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .polar, .matrix => some .optional
    | _, _ => none

/-- All Macedonian question particles indexed in this file. -/
def allQuestionParticles : List Particle := [dali, zar]

end Macedonian.QuestionParticles
