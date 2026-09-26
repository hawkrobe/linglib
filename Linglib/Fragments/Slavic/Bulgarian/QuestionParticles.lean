module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Bulgarian question particles

Bulgarian default polar questions attach the enclitic *li* to the focused constituent, the verb in
a neutral question ([simik-2024] ex. 33). The mirative *nima* is the Bulgarian kin of Russian
*razve* ([simik-2024] §4.2.4). The strategy profile and the bias of *nima* are in
`Studies/Simik2024.lean`.

## References

* [simik-2024]
-/

@[expose] public section

namespace Bulgarian.QuestionParticles

/-- ли *li*, the neutral polar question particle, a second-position enclitic on the focused
constituent. -/
def li : Particle where
  form := "li"
  script := some "ли"
  position := some .secondPosition
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | _, _ => none

/-- нима *nima*, the clause-initial mirative particle, kin of Russian *razve*. -/
def nima : Particle where
  form := "nima"
  script := some "нима"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | _, _ => none

/-- The question particles. -/
def allQuestionParticles : List Particle := [li, nima]

end Bulgarian.QuestionParticles
