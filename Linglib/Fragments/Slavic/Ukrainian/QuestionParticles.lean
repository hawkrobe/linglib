module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Ukrainian question particles

Ukrainian default polar questions are introduced by clause-initial *čy*, which the quiz question
requires ([simik-2024] ex. 29). The mirative *xiba* is the Ukrainian kin of Russian *razve*
([simik-2024] §4.2.4). The strategy profile and the bias of *xiba* are in
`Studies/Simik2024.lean`.

## References

* [simik-2024]
-/

@[expose] public section

namespace Ukrainian.QuestionParticles

/-- чи *čy*, the clause-initial polar question particle. -/
def cy : Particle where
  form := "čy"
  script := some "чи"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .obligatory
    | _, _ => none

/-- хіба *xiba*, the clause-initial mirative particle, kin of Russian *razve*. -/
def xiba : Particle where
  form := "xiba"
  script := some "хіба"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | _, _ => none

/-- The question particles. -/
def allQuestionParticles : List Particle := [cy, xiba]

end Ukrainian.QuestionParticles
