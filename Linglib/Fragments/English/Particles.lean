module

public import Linglib.Syntax.Category.Particle.Basic
public import Linglib.Semantics.Questions.Answering

/-!
# English particles

This file defines the English answer particles and the meta-question adverb *quick*. The
answer particles *yes* and *no* are pro-sentential: *yes* assigns positive and *no* negative
polarity to the elided clause, and English has no polarity-reversing particle. In answer to a
negative question, as Holmberg describes, a bare *no* confirms the negative alternative, *Is
John not coming? No*, and the affirmative answer needs a continuation, *No, he is*, since the
double-negation reading of the bare particle is not taken up. *Quick* or *quickly* before a
question tells the addressee to answer without delay; Dayal groups it with the meta-question
particles, which occur in matrix questions and quotations and are ungrammatical embedded,
*Mary asked Sue quick where she hid the matza*.

## Main definitions

* `English.Particles.yes`, `English.Particles.no`: the answer particles.
* `English.Particles.quick`: the meta-question adverb.

## References

* [holmberg-2016]
* [dayal-2025]
-/

@[expose] public section

namespace English.Particles

/-! ### Answer particles -/

/-- *yes*, the affirmative answer particle. -/
def yes : Question.AnswerParticle := { form := "yes", assigns := .positive }

/-- *no*, the negative answer particle, which alone confirms the negative alternative of a
negative question. -/
def no : Question.AnswerParticle := { form := "no", assigns := .negative }

/-! ### Meta-question adverb -/

/-- *quick* or *quickly* before a question, available in matrix questions and quotations and
excluded from embedded questions. -/
def quick : Particle where
  form := "quick"
  position := some .clauseInitial
  distribution := fun c e ↦ match c with
    | .polar | .alternative | .constituent =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .excluded
      | .quasiSubordinated => some .excluded
      | .quotation => some .optional
      | .insubordinated => none
    | _ => none

end English.Particles
