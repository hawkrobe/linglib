import Linglib.Core.InformationStructure

/-!
# Dutch Polarity Particles

Lexical entries for Dutch sentence-internal polarity particles.

Dutch marks polarity switches (negation → affirmation) primarily via the
affirmative particle *wel*, which appears sentence-internally and carries
a pitch accent. This contrasts with German, which uses Verum focus on the
finite verb (Turco, Braun & Dimroth 2014).

## References

- Turco, G., Braun, B. & Dimroth, C. (2014). How Dutch and German speakers
  produce and realize focus, contrast and correction. *JASA* 136(3), 1400–1414.
- Dimroth, C. (2010). The acquisition of negation. In L. Horn (ed.),
  *The Expression of Negation*, 39–72. de Gruyter.
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
