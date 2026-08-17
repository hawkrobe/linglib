import Linglib.Syntax.Category.Particle.Basic

/-!
# Russian question particles
[esipova-romero-2023] [simik-2024]

Russian marks formal polar questions with the second-position enclitic
*li*, obligatory in subordinated polar questions, while colloquial
matrix polar questions are marked by intonation alone (and can be used
rhetorically, [esipova-romero-2023]). The clause-initial mirative
*razve* is restricted to matrix polar questions ([simik-2024] §4.2.4).
-/

namespace Russian.QuestionParticles

/-- ли li is the neutral polar question particle (formal register), a
second-position enclitic on the focused constituent. -/
def li : Particle where
  form := "li"
  script := some "ли"
  position := some .secondPosition
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | .polar, .subordinated => some .obligatory
    | .constituent, .matrix => some .excluded
    | _, _ => none

/-- разве razve is the mirative/dubitative question particle, signalling
conflict between the speaker's prior epistemic state and current
contextual evidence. -/
def razve_ : Particle where
  form := "razve"
  script := some "разве"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | .polar, .subordinated => some .excluded
    | .constituent, .matrix => some .excluded
    | _, _ => none

/-- All Russian question particles indexed in this file. -/
def allQuestionParticles : List Particle := [li, razve_]

end Russian.QuestionParticles
