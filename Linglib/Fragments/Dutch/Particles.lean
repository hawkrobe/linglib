import Linglib.Typology.PolarityMarking

/-!
# Dutch Polarity Particles
@cite{turco-braun-dimroth-2014}

Lexical entries for Dutch sentence-internal polarity particles.

Dutch marks polarity switches (negation → affirmation) primarily via the
affirmative particle *wel*, which appears sentence-internally and carries
a pitch accent. This contrasts with German, which uses Verum focus on the
finite verb.

-/

namespace Fragments.Dutch.Particles

open Typology.PolarityMarking (PolarityMarkingEntry PolarityMarkingStrategy PolarityMarkingEnv)

/-- *wel* — Dutch affirmative polarity particle.
    Sentence-internal, accented, available in both contrast and correction.
    @cite{turco-braun-dimroth-2014}: dominant strategy in Dutch for neg→affirm switches. -/
abbrev wel : PolarityMarkingEntry where
  label := "wel"
  form := some "wel"
  prosodicTarget := some "particle"
  environments := {.sentenceInternal, .contrast, .correction}
  strategy := .particle

def allPolarityMarkings : List PolarityMarkingEntry := [wel]

-- Per-entry verification theorems
theorem wel_form : wel.form = some "wel" := rfl
theorem wel_sentenceInternal : PolarityMarkingEnv.sentenceInternal ∈ wel.environments := by decide
theorem wel_contrastOk : PolarityMarkingEnv.contrast ∈ wel.environments := by decide
theorem wel_correctionOk : PolarityMarkingEnv.correction ∈ wel.environments := by decide
theorem wel_strategy : wel.strategy = .particle := rfl

end Fragments.Dutch.Particles
