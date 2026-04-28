import Linglib.Typology.PolarityMarking

/-!
# English Polarity-Marking Strategies
@cite{wilder-2013}

English marks polarity reversal (contradiction of a negative assertion)
with emphatic *do* — auxiliary *do* bearing a pitch accent in an
affirmative sentence that contradicts a prior negative claim.

@cite{wilder-2013} distinguishes two uses of emphatic *do*:

1. **Verum-focus *do*** — polarity focus on the truth value of the
   proposition. Contradicts a prior negative assertion.
   "He doesn't like cats." → "He DOES like cats."
   This is the English analogue of German Verum focus.

2. **Contrastive-topic *do*** — *do* marks a contrastive topic shift,
   not polarity focus per se. "He DOES like cats (, but he doesn't
   like dogs)." This use is not polarity-specific and is not modeled
   here.

Only the VF use of emphatic *do* is formalized as a polarity-marking
entry, since it is the strategy that participates in the
polarity-contrast/correction paradigm alongside Dutch *wel* and
German Verum focus.

## Key properties

- Sentence-internal (auxiliary in I°)
- Available in both contrast and correction contexts
- Prosodic: pitch accent falls on *do*
- Strategy: `.verumFocus` — targets the assertion level, like German VF
-/

namespace Fragments.English.PolarityMarking

open Typology.PolarityMarking (PolarityMarkingEntry PolarityMarkingStrategy PolarityMarkingEnv)

/-- Emphatic *do* (Verum-focus use) — English polarity-marking strategy.
    Pitch accent on auxiliary *do* in an affirmative sentence contradicting
    a negative context. Sentence-internal (auxiliary in I°).
    Available in both contrast and correction contexts.
    @cite{wilder-2013}: VF-*do* targets the assertion operator,
    like German Verum focus. -/
abbrev emphaticDo : PolarityMarkingEntry where
  label := "emphatic do"
  prosodicTarget := some "auxiliary do"
  environments := {.sentenceInternal, .contrast, .correction}
  strategy := .verumFocus

def allPolarityMarkings : List PolarityMarkingEntry := [emphaticDo]

-- Per-entry verification theorems
theorem emphaticDo_no_form : emphaticDo.form = none := rfl
theorem emphaticDo_prosodicTarget : emphaticDo.prosodicTarget = some "auxiliary do" := rfl
theorem emphaticDo_sentenceInternal : PolarityMarkingEnv.sentenceInternal ∈ emphaticDo.environments := by decide
theorem emphaticDo_contrastOk : PolarityMarkingEnv.contrast ∈ emphaticDo.environments := by decide
theorem emphaticDo_correctionOk : PolarityMarkingEnv.correction ∈ emphaticDo.environments := by decide
theorem emphaticDo_strategy : emphaticDo.strategy = .verumFocus := rfl

end Fragments.English.PolarityMarking
