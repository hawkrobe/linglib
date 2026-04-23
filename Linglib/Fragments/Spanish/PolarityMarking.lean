import Linglib.Features.InformationStructure

/-!
# Spanish Polarity-Marking Strategies
@cite{batllori-hernanz-2013}

Spanish marks emphatic polarity affirmation with the particle *sí (que)*,
which @cite{batllori-hernanz-2013} analyze as an Emphatic Polarity
Particle of Affirmation (EPPA) merging with ForceP.

## *sí (que)*

- Clause-initial: "Sí que lo sabe" (He DOES know it)
- Contradicts a prior negative assertion or expectation
- *que* is obligatory in embedded contexts and optionally present in root
- Not sentence-internal: the particle precedes the clause

*Sí (que)* is the Spanish reflex of the cross-linguistic class of
polarity-reversing particles (same class as French *si*, German *doch*,
Swedish *jo*; @cite{holmberg-2016}).

## Contrast with English

English emphatic *do* is sentence-internal (auxiliary in I°) and targets
the assertion level via prosodic prominence. Spanish *sí (que)* is
clause-initial and targets polarity directly via a dedicated particle.
-/

namespace Fragments.Spanish.PolarityMarking

open Features.InformationStructure (PolarityMarkingEntry PolarityMarkingStrategy)

/-- *sí (que)* — Spanish emphatic polarity affirmation particle.
    Clause-initial EPPA that contradicts a negative context.
    @cite{batllori-hernanz-2013}: merges with ForceP; *que* is
    obligatory in embedded contexts. Not sentence-internal.
    Correction-only: requires a negative context to reverse. -/
def siQue : PolarityMarkingEntry where
  label := "sí (que)"
  form := some "sí (que)"
  sentenceInternal := false
  contrastOk := false
  correctionOk := true
  strategy := .polarityReversal

def allPolarityMarkings : List PolarityMarkingEntry := [siQue]

-- Per-entry verification theorems
theorem siQue_form : siQue.form = some "sí (que)" := rfl
theorem siQue_not_sentenceInternal : siQue.sentenceInternal = false := rfl
theorem siQue_not_contrastOk : siQue.contrastOk = false := rfl
theorem siQue_correctionOk : siQue.correctionOk = true := rfl
theorem siQue_strategy : siQue.strategy = .polarityReversal := rfl

end Fragments.Spanish.PolarityMarking
