module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Macedonian question particles

Macedonian default polar questions are introduced by clause-initial *dali*, which admits negation
without inducing bias ([simik-2024] ex. 32), or carry the enclitic *li* on the fronted verb, which
is reported to convey surprise or a negative answer expectation, unlike Bulgarian and Russian *li*
([simik-2024] §4.2.5). The mirative *zar* is the Macedonian kin of Russian *razve* ([simik-2024]
§4.2.4). The strategy profiles are in `Studies/Simik2024.lean`.

## References

* [simik-2024]
-/

@[expose] public section

namespace Macedonian.QuestionParticles

/-- дали *dali*, the clause-initial polar question particle. -/
def dali : Particle where
  form := "dali"
  script := some "дали"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | _, _ => none

/-- ли *li*, the polar question particle enclitic on the fronted verb, whose negated form conveys
positive epistemic bias ([simik-2024] ex. 32b). -/
def li : Particle where
  form := "li"
  script := some "ли"
  position := some .secondPosition
  distribution := fun c e => match c, e with
    | .polar, .matrix => some .optional
    | _, _ => none

/-- зар *zar*, the clause-initial mirative particle, kin of Russian *razve*. -/
def zar : Particle where
  form := "zar"
  script := some "зар"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .polar, .matrix => some .optional
    | _, _ => none

/-- The question particles. -/
def allQuestionParticles : List Particle := [dali, li, zar]

end Macedonian.QuestionParticles
