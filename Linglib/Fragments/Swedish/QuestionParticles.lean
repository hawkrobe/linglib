/-!
# Swedish Question Particles
@cite{seeliger-repp-2018}

Lexical entries for Swedish modal particles that occur in declarative
questions. The fragment commits only to theory-neutral lexical primitives;
the left-peripheral layer assignment lives in
`Phenomena.Questions.Studies.SeeligerRepp2018`.

## Particles

| Particle | Function | Position | DQ type |
|----------|----------|----------|---------|
| väl | question-inducing modal particle | clause-medial (after finite V) | PDQ / NRQ |

Swedish *väl* signals that the speaker is not certain about the
proposition but suspects it to be true, and expects confirmation from
the addressee. It is functionally similar to German *wohl* but unlike
*wohl*, *väl* can also occur in rejecting questions (NRQs) when
combined with fronted negation.

Crucially, *väl* is distinct from *jo* (in `AnswerParticles.lean`):
- *jo* is a polarity-reversing answer particle — it answers negative
  questions with positive polarity
- *väl* is a modal particle that turns declaratives into questions —
  it marks speaker uncertainty and invites addressee confirmation

## Other Swedish particles

Swedish also has clause-initial *visst* and *nog* which can mark PRQs,
but these are not formalized here. @cite{seeliger-repp-2018} note that
*visst*/*nog* have no overlap in meaning with *väl* in clause-medial
position, and their clause-initial uses require further investigation.

## Cross-Module Connections

- `Fragments.Swedish.AnswerParticles`: *jo* (polarity reversal, not DQ marking)
- `Fragments.German.QuestionParticles`: *doch wohl* (German RQ marker)
- `Semantics.Questions.DeclarativeQuestions`: bias profile typology
-/

namespace Fragments.Swedish.QuestionParticles

/-- A Swedish question/modal particle entry. -/
structure QParticleEntry where
  form : String
  gloss : String
  /-- Compatible with polar questions (declarative syntax)? -/
  polarOk : Bool
  /-- Compatible with declarative assertions? -/
  declOk : Bool
  /-- Compatible with wh-questions? -/
  whOk : Bool
  /-- Does this particle require evidential bias (contextual evidence)? -/
  requiresEvidentialBias : Bool
  /-- Does this particle signal epistemic uncertainty? -/
  signalsEpistemicUncertainty : Bool
  /-- Is this particle question-inducing? -/
  questionInducing : Bool
  deriving Repr, DecidableEq

/-- *väl* — question-inducing modal particle.

    @cite{seeliger-repp-2018} SS 5.2: *väl* signals that the speaker is not
    certain about the proposition but suspects it to be true. The speaker
    expects a confirmation from the addressee. Declaratives with *väl*
    cannot be assertions — they are declarative questions.

    Positive *väl*-declaratives have the bias profile of PDQs:
    evidential [+positive], epistemic [-positive].

    When combined with fronted negation (*inte*), *väl* can mark NRQs:
    "Inte kommer Peter?" / "Peter kommer väl inte?" -/
def val : QParticleEntry where
  form := "väl"
  gloss := "MP (question-inducing uncertainty particle)"
  polarOk := true
  declOk := false  -- väl-declaratives are questions, not assertions
  whOk := false
  requiresEvidentialBias := true
  signalsEpistemicUncertainty := true
  questionInducing := true

def allQuestionParticles : List QParticleEntry := [val]

-- Verification theorems
theorem val_form : val.form = "väl" := rfl
theorem val_question_inducing : val.questionInducing = true := rfl
theorem val_signals_uncertainty : val.signalsEpistemicUncertainty = true := rfl
theorem val_requires_evidential : val.requiresEvidentialBias = true := rfl
theorem val_not_assertion : val.declOk = false := rfl

end Fragments.Swedish.QuestionParticles
