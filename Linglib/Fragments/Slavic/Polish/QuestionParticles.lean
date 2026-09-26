module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Polish question particles

Polish default polar questions are introduced by clause-initial *czy*, which the quiz question
requires ([simik-2024] ex. 30); declarative polar questions without it are grammatical but carry
evidential bias. The mirative *czyżby* is the Polish kin of Russian *razve* ([simik-2024] §4.2.4).
The strategy profile and the bias of *czyżby* are in `Studies/Simik2024.lean`.

## References

* [simik-2024]
-/

@[expose] public section

namespace Polish.QuestionParticles

/-- *czy*, the clause-initial polar question particle. -/
def czy : Particle where
  form := "czy"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .obligatory
    | _, _ => none

/-- *czyżby*, the clause-initial mirative particle, kin of Russian *razve*. -/
def czyzby : Particle where
  form := "czyżby"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | _, _ => none

/-- The question particles. -/
def allQuestionParticles : List Particle := [czy, czyzby]

end Polish.QuestionParticles
