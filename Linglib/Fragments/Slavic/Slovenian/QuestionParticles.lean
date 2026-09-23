module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Slovenian Question Particles
[simik-2024]

The Slovenian clause-initial polar question particles: *ali* of the
default (quiz-felicitous) strategy, and the colloquial *a* and *kaj*,
which the quiz scenario excludes. Bias profiles live in `Simik2024`.

## Cross-Module Connections

- `Simik2024.slovenian` (`Studies/Simik2024`): PQ strategy profile
-/

@[expose] public section

namespace Slovenian.QuestionParticles

/-- ali — clause-initial PQ particle ([simik-2024] ex. 28). Optional in
default PQs; incompatible with DeclPQs. -/
def ali : Particle where
  form := "ali"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | .constituent, .matrix => some .excluded
    | _, _ => none

/-- *a* — colloquial clause-initial PQ particle, neutral yet excluded from
the quiz scenario ([simik-2024] §4.1). -/
def a : Particle where
  form := "a"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .polar, .matrix => some .optional
    | _, _ => none

/-- *kaj* (lit. 'what') — clause-initial PQ particle excluded from the
quiz scenario ([simik-2024] §4.1). -/
def kaj : Particle where
  form := "kaj"
  position := some .clauseInitial
  distribution := a.distribution

end Slovenian.QuestionParticles
