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
  produce and realize focus, brat and correction. *JASA* 136(3), 1400–1414.
- Dimroth, C. (2010). The acquisition of negation. In L. Horn (ed.),
  *The Expression of Negation*, 39–72. de Gruyter.
-/

namespace Fragments.Dutch.Particles

open Core.InformationStructure (PolaritySwitchContext PolarityMarkingStrategy)

/-- A Dutch polarity particle entry. -/
structure PolarityParticleEntry where
  /-- Surface form -/
  form : String
  /-- English gloss -/
  gloss : String
  /-- Whether the particle carries a pitch accent -/
  accented : Bool
  /-- Whether the particle appears sentence-internally (vs. pre-utterance) -/
  sentenceInternal : Bool
  /-- Available in contrast contexts (Klein 2008) -/
  contrastOk : Bool
  /-- Available in correction contexts (Umbach 2004) -/
  correctionOk : Bool
  /-- The polarity-marking strategy this particle instantiates -/
  strategy : PolarityMarkingStrategy
  deriving Repr, DecidableEq, BEq

/-- *wel* — Dutch affirmative polarity particle.
    Sentence-internal, accented, available in both contrast and correction.
    Turco et al. (2014): dominant strategy in Dutch for neg→affirm switches. -/
def wel : PolarityParticleEntry where
  form := "wel"
  gloss := "indeed / AFF"
  accented := true
  sentenceInternal := true
  contrastOk := true
  correctionOk := true
  strategy := .particle

def allPolarityParticles : List PolarityParticleEntry := [wel]

-- Per-entry verification theorems
theorem wel_accented : wel.accented = true := rfl
theorem wel_sentenceInternal : wel.sentenceInternal = true := rfl
theorem wel_contrastOk : wel.contrastOk = true := rfl
theorem wel_correctionOk : wel.correctionOk = true := rfl
theorem wel_strategy : wel.strategy = .particle := rfl

end Fragments.Dutch.Particles
