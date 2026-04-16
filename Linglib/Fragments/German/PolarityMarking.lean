import Linglib.Core.Discourse.InformationStructure

/-!
# German Polarity-Marking Strategies
@cite{turco-braun-dimroth-2014} @cite{hohle-1992} @cite{romero-han-2004}

Lexical entries for how German marks polarity switches (negation → affirmation).

The key finding of @cite{turco-braun-dimroth-2014} is that German does NOT use
sentence-internal particles for polarity switches. Instead, German relies on
Verum focus: a pitch accent on the finite verb. The particle
*doch* can appear pre-utterance in corrections but is not sentence-internal
in the relevant sense.

This file is named "PolarityMarking" rather than "Particles" precisely because
German's strategy is non-particulate.

## Cross-Module Connections

- `Semantics.Questions.VerumFocus`: VERUM in questions — a
  different phenomenon from the declarative Verum focus encoded here
- `Fragments.German.QuestionParticles`: German *denn* (question-flavoring)

-/

namespace Fragments.German.PolarityMarking

open Core.InformationStructure (PolarityMarkingEntry PolarityMarkingStrategy)

/-- Verum focus — pitch accent on the finite verb.
    Dominant strategy in German for neg→affirm switches in both contexts.
    Sentence-internal; available in both contrast and correction.
    @cite{hohle-1992}, @cite{turco-braun-dimroth-2014}: ~82% in contrast,
    ~78% in correction. -/
def verumFocus : PolarityMarkingEntry where
  label := "Verum focus"
  prosodicTarget := some "finite verb"
  sentenceInternal := true
  contrastOk := true
  correctionOk := true
  strategy := .verumFocus

/-- *doch* — polarity-reversing correction particle (@cite{holmberg-2016}).
    Assigns [+Pol] while contradicting a negative context. Available only
    in corrections, NOT sentence-internal in the sense of
    @cite{turco-braun-dimroth-2014}: it precedes the utterance rather than
    appearing within the VP/middle field. Cross-linguistically the same
    class as Swedish *jo* and French *si*. -/
def dochPreUtterance : PolarityMarkingEntry where
  label := "doch (pre-utterance)"
  form := some "doch"
  sentenceInternal := false
  contrastOk := false
  correctionOk := true
  strategy := .polarityReversal

def allPolarityMarkings : List PolarityMarkingEntry := [verumFocus, dochPreUtterance]

-- Per-entry verification theorems: verumFocus
theorem vf_prosodicTarget : verumFocus.prosodicTarget = some "finite verb" := rfl
theorem vf_sentenceInternal : verumFocus.sentenceInternal = true := rfl
theorem vf_contrastOk : verumFocus.contrastOk = true := rfl
theorem vf_correctionOk : verumFocus.correctionOk = true := rfl
theorem vf_strategy : verumFocus.strategy = .verumFocus := rfl

-- Per-entry verification theorems: dochPreUtterance
theorem doch_form : dochPreUtterance.form = some "doch" := rfl
theorem doch_not_sentenceInternal : dochPreUtterance.sentenceInternal = false := rfl
theorem doch_not_contrastOk : dochPreUtterance.contrastOk = false := rfl
theorem doch_correctionOk : dochPreUtterance.correctionOk = true := rfl
theorem doch_strategy : dochPreUtterance.strategy = .polarityReversal := rfl

end Fragments.German.PolarityMarking
