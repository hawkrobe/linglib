import Linglib.Core.InformationStructure

/-!
# German Polarity-Marking Strategies

Lexical entries for how German marks polarity switches (negation → affirmation).

The key finding of Turco, Braun & Dimroth (2014) is that German does NOT use
sentence-internal particles for polarity switches. Instead, German relies on
Verum focus: a pitch accent on the finite verb (Höhle 1992). The particle
*doch* can appear pre-utterance in corrections but is not sentence-internal
in the relevant sense.

This file is named "PolarityMarking" rather than "Particles" precisely because
German's strategy is non-particulate.

## Cross-Module Connections

- `Semantics.Questions.VerumFocus`: VERUM in questions (Romero & Han 2004) — a
  different phenomenon from the declarative Verum focus (Höhle 1992) encoded here
- `Fragments.German.QuestionParticles`: German *denn* (question-flavoring)

## References

- Turco, G., Braun, B. & Dimroth, C. (2014). How Dutch and German speakers
  produce and realize focus, contrast and correction. *JASA* 136(3), 1400–1414.
- Höhle, T. (1992). Über Verum-Fokus im Deutschen. In J. Jacobs (ed.),
  *Informationsstruktur und Grammatik*, 112–141. Westdeutscher Verlag.
-/

namespace Fragments.German.PolarityMarking

open Core.InformationStructure (PolarityMarkingEntry PolarityMarkingStrategy)

/-- Verum focus — pitch accent on the finite verb (Höhle 1992).
    Dominant strategy in German for neg→affirm switches in both contexts. -/
def verumFocus : PolarityMarkingEntry where
  label := "Verum focus"
  prosodicTarget := some "finite verb"
  sentenceInternal := true
  contrastOk := true
  correctionOk := true
  strategy := .verumFocus

/-- *doch* — pre-utterance correction particle.
    Available only in corrections, NOT sentence-internal in the sense of
    Turco et al. (2014): it precedes the utterance rather than appearing
    within the VP/middle field. -/
def dochPreUtterance : PolarityMarkingEntry where
  label := "doch (pre-utterance)"
  form := some "doch"
  sentenceInternal := false
  contrastOk := false
  correctionOk := true
  strategy := .other

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
theorem doch_strategy : dochPreUtterance.strategy = .other := rfl

end Fragments.German.PolarityMarking
