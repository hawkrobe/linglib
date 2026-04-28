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

open Typology.PolarityMarking (Entry Strategy Env)

/-- *wel* — Dutch affirmative polarity particle.
    Sentence-internal, accented, available in both contrast and correction.
    @cite{turco-braun-dimroth-2014}: dominant strategy in Dutch for neg→affirm switches. -/
abbrev wel : Entry where
  label := "wel"
  form := some "wel"
  prosodicTarget := some "particle"
  environments := {.sentenceInternal, .contrast, .correction}
  strategy := .particle

def allPolarityMarkings : List Entry := [wel]

-- Per-entry verification theorems
theorem wel_form : wel.form = some "wel" := rfl
theorem wel_sentenceInternal : Env.sentenceInternal ∈ wel.environments := by decide
theorem wel_contrastOk : Env.contrast ∈ wel.environments := by decide
theorem wel_correctionOk : Env.correction ∈ wel.environments := by decide
theorem wel_strategy : wel.strategy = .particle := rfl

end Fragments.Dutch.Particles
