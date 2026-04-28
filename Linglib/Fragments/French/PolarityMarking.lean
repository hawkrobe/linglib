import Linglib.Typology.PolarityMarking

/-!
# French Polarity-Marking Strategies
@cite{holmberg-2016}

French marks polarity reversal (contradiction of a negative assertion or
question) with the dedicated particle *si*. Like German *doch* and
Swedish *jo*, *si* assigns [+Pol] while presupposing a negative context.

Unlike Dutch *wel*, *si* is not sentence-internal: it appears clause-
initially or as a standalone response.

## Examples

- "Tu ne viens pas?" (You're not coming?)
  → "Si (, je viens)." (Yes I am.)

- "Il ne pleut pas." (It's not raining.)
  → "Si (, il pleut.)" (Yes it is.)

*Si* cannot be used without a negative context:
- "Tu viens?" (Are you coming?)
  → *"Si" (infelicitous — no negation to reverse; use *oui*)

## Cross-linguistic class

@cite{holmberg-2016}: *si*, *jo*, *doch* form a natural class of
polarity-reversing particles — they assign [+Pol] in contexts where
a negative polarity is salient. This class is distinct from plain
affirmative particles like Dutch *wel* and from Verum focus.
-/

namespace Fragments.French.PolarityMarking

open Typology.PolarityMarking (Entry Strategy Env)

/-- *si* — French polarity-reversing affirmative particle.
    Assigns [+Pol] while contradicting a negative assertion or question.
    Clause-initial or standalone; not sentence-internal.
    Correction-only: requires a negative context to reverse. -/
abbrev si : Entry where
  label := "si"
  form := some "si"
  environments := {.correction}
  strategy := .polarityReversal

def allPolarityMarkings : List Entry := [si]

-- Per-entry verification theorems
theorem si_form : si.form = some "si" := rfl
theorem si_not_sentenceInternal : Env.sentenceInternal ∉ si.environments := by decide
theorem si_not_contrastOk : Env.contrast ∉ si.environments := by decide
theorem si_correctionOk : Env.correction ∈ si.environments := by decide
theorem si_strategy : si.strategy = .polarityReversal := rfl

end Fragments.French.PolarityMarking
