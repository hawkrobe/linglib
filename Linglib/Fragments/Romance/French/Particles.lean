module

public import Linglib.Semantics.Questions.Answering

/-!
# French answer particles

The answer particles *oui*, *non* and *si*, pro-sentential and typed by
`Question.AnswerParticle`. *Oui* assigns positive and *non* negative polarity. *Si*, glossed
yes.REV, is the polarity-reversing affirmative: after a negative question it replaces *oui*,
which cannot confirm the positive alternative, *Tu n'es pas fatigué? — \*Oui / Si*
([holmberg-2016]). It reverses a negative assertion as well, *Il ne fait pas beau. — Si (il fait
beau)*, and [farkas-bruce-2010] characterize it as marking the combination of reverse relative
polarity and positive absolute polarity. Unlike the Italian *sì che* and Spanish *sí que*
constructions, *si* is limited to answering a preceding opposite turn ([garassino-jacob-2018]),
which is what the REV feature requires: there must be a negation for it to eliminate.

## References

* [holmberg-2016]
* [farkas-bruce-2010]
* [garassino-jacob-2018]
-/

@[expose] public section

namespace French.Particles

/-- *oui* 'yes', the affirmative answer particle: *Tu es fatigué?* 'Are you tired?' — *Oui*. -/
def oui : Question.AnswerParticle := { form := "oui", assigns := .positive }

/-- *non* 'no', the negative answer particle. -/
def non : Question.AnswerParticle := { form := "non", assigns := .negative }

/-- *si* 'yes.REV', the polarity-reversing affirmative: *Tu n'es pas fatigué?* 'Are you not
tired?' — *Si*, I am. -/
def si : Question.AnswerParticle := { form := "si", assigns := .positive, reverses := true }

end French.Particles
