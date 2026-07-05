import Linglib.Syntax.Particle.Basic

/-!
# Swedish Question Particles
[seeliger-repp-2018]

Lexical entry for Swedish *väl* as a `Particle` value. *väl* is a
clause-medial modal particle that turns declaratives into questions:
it signals speaker uncertainty and invites addressee confirmation.
Functionally similar to German *wohl*, but unlike *wohl* it can occur in
rejecting questions (NRQs) when combined with fronted negation. Its bias
profile and the PDQ/NRQ analysis live in `SeeligerRepp2018`.

Crucially, *väl* is distinct from *jo* (in `AnswerParticles.lean`):
*jo* is a polarity-reversing answer particle; *väl* marks declarative
questions.

## Other Swedish particles

Swedish also has clause-initial *visst* and *nog* which can mark PRQs,
but these are not formalized here. [seeliger-repp-2018] note that
*visst* and *nog* have no overlap in meaning with *väl* in clause-medial
position, and their clause-initial uses require further investigation.
-/

namespace Swedish.QuestionParticles

/-- *väl* — question-inducing modal particle, clause-medial (after the
finite verb): declarative-syntax polar questions (recorded under
`polarInterrogative` following the source schema's question-function
reading), not plain assertions, not wh-questions. Epistemic-uncertainty
signal and evidential bias live in `SeeligerRepp2018`. -/
def val : Particle where
  form := "väl"
  position := .clauseMedial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

def allQuestionParticles : List Particle := [val]

end Swedish.QuestionParticles
