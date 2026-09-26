module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Turkish question particles

Turkish forms yes/no questions and alternative questions with the clitic *mI*, written as a
separate word and harmonizing with the preceding vowel as *mı*, *mi*, *mu* or *mü*
([goksel-kerslake-2005] §11.1, §11.1.1.5). It attaches to the predicate when the whole
proposition is questioned and can instead attach to a subject, object or adverbial (§19.1.1,
§19.1.3); in an alternative question it follows each alternative (§19.1.2). It is obligatory
in polar questions ([turk-hirsch-2026]). Indirect alternative questions keep *mI* after each
alternative, while indirect yes/no questions are formed with the -(y)Ip…-mA construction
instead (§24.4.3.2).

## References

* [goksel-kerslake-2005]
* [turk-hirsch-2026]
-/

@[expose] public section

namespace Turkish.QuestionParticles

/-- *mI*, the enclitic that forms yes/no and alternative questions. -/
def mi : Particle where
  form := "mI"
  position := some .postHost
  distribution
    | .polar, .matrix => some .obligatory
    | .alternative, .matrix => some .obligatory
    | .alternative, .subordinated => some .obligatory
    | _, _ => none

end Turkish.QuestionParticles
