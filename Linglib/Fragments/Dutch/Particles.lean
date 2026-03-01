import Linglib.Core.Discourse.InformationStructure

/-!
# Dutch Polarity Particles
@cite{dimroth-2010} @cite{turco-braun-dimroth-2014}

Lexical entries for Dutch sentence-internal polarity particles.

Dutch marks polarity switches (negation → affirmation) primarily via the
affirmative particle *wel*, which appears sentence-internally and carries
a pitch accent. This contrasts with German, which uses Verum focus on the
finite verb (Turco, Braun & Dimroth 2014).

-/

namespace Fragments.Dutch.Particles

open Core.InformationStructure (PolarityMarkingEntry PolarityMarkingStrategy)

/-- *wel* — Dutch affirmative polarity particle.
    Sentence-internal, accented, available in both contrast and correction.
    Turco et al. (2014): dominant strategy in Dutch for neg→affirm switches. -/
def wel : PolarityMarkingEntry where
  label := "wel"
  form := some "wel"
  prosodicTarget := some "particle"
  sentenceInternal := true
  contrastOk := true
  correctionOk := true
  strategy := .particle

def allPolarityParticles : List PolarityMarkingEntry := [wel]

-- Per-entry verification theorems
theorem wel_form : wel.form = some "wel" := rfl
theorem wel_sentenceInternal : wel.sentenceInternal = true := rfl
theorem wel_contrastOk : wel.contrastOk = true := rfl
theorem wel_correctionOk : wel.correctionOk = true := rfl
theorem wel_strategy : wel.strategy = .particle := rfl

end Fragments.Dutch.Particles
