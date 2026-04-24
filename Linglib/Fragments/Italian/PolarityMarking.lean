import Linglib.Features.InformationStructure

/-!
# Italian Polarity-Marking Strategies
@cite{garassino-jacob-2018}

Italian marks emphatic polarity affirmation with the construction *sì che*,
the direct cognate of Spanish *sí que*. Like its Spanish counterpart,
*sì che* is a cleft-like construction containing the affirmative polarity
particle *sì* followed by the complementizer *che*.

## Examples

- "È poi arrivato Gianni?" (Has Gianni arrived?)
  → "Sì che è arrivato." (He HAS arrived / Of course he has.)

- "No ha cantado la soprano." (The soprano didn't sing.)
  → "Sí que ha cantado la soprano." (She DID sing.)
  (Spanish cognate, from @cite{batllori-hernanz-2013})

## Corpus evidence

@cite{garassino-jacob-2018} Table 1: in the Direct Europarl corpus,
Italian has 0 *sì che* occurrences vs. 61 Spanish *sí que* occurrences.
Italian speakers prefer other strategies (clitic left dislocation, echo
replies) for polarity contrast. However, *sì che* is well-attested in
the literature (Bernini 1995; Poletto & Zanuttini 2013) and in
translations of speeches from other languages.

## Cross-linguistic class

*Sì che* belongs to the same class as Spanish *sí que*, French *si*,
German *doch*, and Swedish *jo*: polarity-reversing particles that
assign [+Pol] in contexts where a negative polarity is salient.
-/

namespace Fragments.Italian.PolarityMarking

open Features.InformationStructure (PolarityMarkingEntry PolarityMarkingStrategy PolarityMarkingEnv)

/-- *sì che* — Italian polarity-reversing affirmative construction.
    Cleft-like structure: affirmative particle *sì* + complementizer *che*.
    Clause-initial; not sentence-internal.
    Correction-only: requires a negative context to reverse.
    @cite{garassino-jacob-2018}: cognate of Spanish *sí que*;
    rare in corpus data but grammatically available. -/
abbrev siChe : PolarityMarkingEntry where
  label := "sì che"
  form := some "sì che"
  environments := {.correction}
  strategy := .polarityReversal

def allPolarityMarkings : List PolarityMarkingEntry := [siChe]

-- Per-entry verification theorems
theorem siChe_form : siChe.form = some "sì che" := rfl
theorem siChe_not_sentenceInternal : PolarityMarkingEnv.sentenceInternal ∉ siChe.environments := by decide
theorem siChe_not_contrastOk : PolarityMarkingEnv.contrast ∉ siChe.environments := by decide
theorem siChe_correctionOk : PolarityMarkingEnv.correction ∈ siChe.environments := by decide
theorem siChe_strategy : siChe.strategy = .polarityReversal := rfl

end Fragments.Italian.PolarityMarking
