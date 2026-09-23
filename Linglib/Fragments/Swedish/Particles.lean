module

public import Linglib.Syntax.Category.Particle.Basic
public import Linglib.Semantics.Questions.Answering

/-!
# Swedish particles

The modal particle *väl* and the answer particles *ja*, *nej* and *jo*.

*Väl* is a clause-medial modal particle of declaratives: the speaker suspects but is not
certain that the proposition is true and expects the addressee to take a stance on it, so that
a declarative with *väl* is a question rather than an assertion ([seeliger-repp-2018]). Unlike
German *wohl* it lacks a reportative meaning. Its role in rejecting questions, with low negation
and with *men* 'but', is analysed in `SeeligerRepp2018`. Swedish also has clause-initial *visst*
and *nog*, which can mark positive rejecting questions and are not formalized here.

The answer particles are pro-sentential and typed by `Question.AnswerParticle`: *ja* assigns
positive and *nej* negative polarity, and *jo*, glossed yes.REV, is the polarity-reversing
affirmative that confirms the positive alternative of a negative question ([holmberg-2016]).

## References

* [seeliger-repp-2018]
* [holmberg-2016]
-/

@[expose] public section

namespace Swedish.Particles

/-! ### Modal particles -/

/-- *väl* — clause-medial modal particle (after the finite verb) of matrix declaratives. That a
declarative with *väl* is a question and not an assertion is a matter of speech act, not of
clause type, analysed in `SeeligerRepp2018`. -/
def val : Particle where
  form := "väl"
  position := some .clauseMedial
  distribution := fun c e ↦ match c, e with
    | .declarative, .matrix => some .optional
    | _, _ => none

/-! ### Answer particles -/

/-- *ja* 'yes', the affirmative answer particle: *Vill han ha kaffe?* 'Does he want coffee?' —
*Ja*. -/
def ja : Question.AnswerParticle := { form := "ja", assigns := .positive }

/-- *nej* 'no', the negative answer particle: *Har Johan inte kommit?* 'Has Johan not
arrived?' — *Nej*, he has not. -/
def nej : Question.AnswerParticle := { form := "nej", assigns := .negative }

/-- *jo* 'yes.REV', the polarity-reversing affirmative: *Har Johan inte kommit?* — *Jo*, he
has. -/
def jo : Question.AnswerParticle := { form := "jo", assigns := .positive, reverses := true }

end Swedish.Particles
