import Linglib.Syntax.Category.Particle.Basic

/-!
# Mandarin question particles

Mandarin marks polar questions with the neutral sentence-final particle
*ma* 吗 and the confirmation-seeking *ba* 吧; both attach to declarative
word order, and neither forms constituent questions — *wh*-words stay in
situ, and under *ma* a *wh*-word takes only its indefinite reading, so
the string remains a polar question. The clause-initial evidential
adverb *nándào* 难道 forms surprise polar questions and is incompatible
with declaratives and *wh*-questions. This file provides the three as
`Particle` values with recorded licensing distributions; *nandao*'s
evidential felicity conditions live with their analysis.

## Main declarations

* `Mandarin.QuestionParticles.ma` — the neutral polar question particle.
* `Mandarin.QuestionParticles.ba` — the confirmation-seeking particle.
* `Mandarin.QuestionParticles.nandao` — the evidential question adverb.

## References

* [li-thompson-1981]
* [xu-2012]
* [zheng-2025]
-/

namespace Mandarin.QuestionParticles

/-- *ma* 吗 is the neutral sentence-final polar question particle. -/
def ma : Particle where
  form := "ma"
  script := some "吗"
  position := some .clauseFinal
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | .constituent, .matrix => some .excluded
    | _, _ => none

/-- *ba* 吧 is the confirmation-seeking question particle, distinct from
the homophonous suggestion-softening *ba* of imperatives. -/
def ba : Particle where
  form := "ba"
  script := some "吧"
  position := some .clauseFinal
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | .constituent, .matrix => some .excluded
    | _, _ => none

/-- *nándào* 难道 is a clause-initial evidential adverb forming surprise
polar questions. -/
def nandao : Particle where
  form := "nándào"
  script := some "难道"
  position := some .clauseInitial
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | .constituent, .matrix => some .excluded
    | _, _ => none

/-- All Mandarin question particles indexed in this file. -/
def allQuestionParticles : List Particle := [ma, ba, nandao]

end Mandarin.QuestionParticles
