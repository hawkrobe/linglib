module

public import Linglib.Syntax.Category.Particle.Basic
public import Linglib.Semantics.Questions.Answering

/-!
# Swedish particles

The modal particle *väl* and the answer particles *ja*, *nej* and *jo*.

*Väl* is a clause-medial modal particle that turns declaratives into questions: it signals
speaker uncertainty and invites confirmation ([seeliger-repp-2018]). It is functionally similar
to German *wohl*, but unlike *wohl* it can occur in rejecting questions combined with fronted
negation; its bias profile and the analysis of declarative questions live in
`SeeligerRepp2018`. Swedish also has clause-initial *visst* and *nog*, which can mark
positive rejecting questions and are not formalized here.

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

/-- *väl* — question-inducing modal particle, clause-medial (after the finite verb):
declarative-syntax polar questions (recorded under the polar clause type, following the source
schema's question-function reading), not plain assertions, not wh-questions.
Epistemic-uncertainty signal and evidential bias live in `SeeligerRepp2018`. -/
def val : Particle where
  form := "väl"
  position := some .clauseMedial
  distribution := fun c e ↦ match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | .constituent, .matrix => some .excluded
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
