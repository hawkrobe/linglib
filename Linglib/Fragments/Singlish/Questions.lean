import Mathlib.Data.Finset.Insert
import Linglib.Syntax.Category.WhModifier
import Linglib.Syntax.Category.Particle.Basic
import Linglib.Syntax.Question

/-!
# Singlish questions

Colloquial Singapore English forms a content question three interchangeable ways
([sato-2013]): full wh-movement (*What you think Natalie is baking at 3am ah?*), partial
movement to an intermediate Spec-CP (*You think what Natalie is baking at 3am ah?*), and
wh-in-situ (*You think Natalie is baking what at 3am ah?*), with do-support optional and the
clause-final particle *ah* keeping an in-situ question from an echo reading. Full and partial
movement put the wh-phrase in matrix Spec-CP, the latter by a covert second step that is
island-sensitive; an in-situ wh-phrase is bound unselectively and never moves
([sato-ngui-2017]). *The-hell* adjoins to the wh-head and moves only with it
([chan-shen-2026]).

## References

* [sato-2013]
* [sato-ngui-2017]
* [chan-shen-2026]
-/

namespace Singlish.Questions

open Syntax.Question WhModifier

/-- The three question-formation strategies: full movement, partial movement, in situ. -/
def strategies : Finset WhInterpMechanism :=
  {.overtMovement, .partialMovement, .unselectiveBinding}

/-- *ah*: the clause-final particle that blocks the echo reading of a wh-in-situ question. -/
def ah : Particle where
  form := "ah"
  position := some .clauseFinal
  distribution := λ c e => match c, e with
    | .constituent, .matrix => some .optional
    | _, _ => none

/-- *the hell*: adjoined to the wh-head, so it reaches Spec-CP only on the wh-phrase. -/
def theHell : WhModifier :=
  { form := "the hell", gloss := "the-hell", mobility := .parasitic }

end Singlish.Questions
