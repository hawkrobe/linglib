import Linglib.Typology.PolarityMarking

/-!
# Spanish Polarity-Marking Strategies
@cite{batllori-hernanz-2013} @cite{garassino-jacob-2018}

Spanish marks emphatic polarity affirmation with the particle *sí (que)*,
which @cite{batllori-hernanz-2013} analyze as an Emphatic Polarity
Particle of Affirmation (EPPA) merging with ForceP.

## *sí (que)*

- Clause-initial: "Sí que lo sabe" (He DOES know it)
- Licensed in both *contrast* (positive answer to a yes/no question) and
  *correction* (denying a prior negative assertion) contexts;
  @cite{batllori-hernanz-2013} ex. 4-5 and @cite{garassino-jacob-2018}
  ex. 19 show *sí que* in non-contradictory contexts (e.g.,
  "Carrefour le ofrece este fin de semana precios de vértigo… ¡Esto sí
  que es un aniversario!"). The earlier `correction`-only encoding was
  empirically too narrow.
- *que* is obligatory in embedded contexts and optionally present in root
- Not sentence-internal: the particle precedes the clause

*Sí (que)* is the Spanish reflex of a *functional* class of
polarity-reversing markers, but the cross-linguistic lumping with
French *si*, German *doch*, and Swedish *jo* obscures syntactic
differences. Per @cite{garassino-jacob-2018} fn 11, French *si* is
restricted to dialogical contexts (response to a preceding negative
turn) — making it a response particle, not a clause-initial
construction comparable to *sí que* / *sì che*.

## Contrast with English

English emphatic *do* is sentence-internal (auxiliary in I°) and targets
the assertion level via prosodic prominence. Spanish *sí (que)* is
clause-initial and targets polarity directly via a dedicated particle.
-/

namespace Fragments.Spanish.PolarityMarking

open Typology.PolarityMarking (Entry Strategy Env)

/-- *sí (que)* — Spanish emphatic polarity affirmation particle.
    Clause-initial EPPA. @cite{batllori-hernanz-2013}: merges with
    ForceP; *que* is obligatory in embedded contexts. Licensed in
    both contrast and correction environments per Batllori & Hernanz
    ex. 4-5 + @cite{garassino-jacob-2018} ex. 19. Not sentence-internal. -/
abbrev siQue : Entry where
  label := "sí (que)"
  form := some "sí (que)"
  environments := {.correction, .contrast}
  strategy := .polarityReversal

def allPolarityMarkings : List Entry := [siQue]

-- Per-entry verification theorems
theorem siQue_form : siQue.form = some "sí (que)" := rfl
theorem siQue_not_sentenceInternal : Env.sentenceInternal ∉ siQue.environments := by decide
theorem siQue_contrastOk : Env.contrast ∈ siQue.environments := by decide
theorem siQue_correctionOk : Env.correction ∈ siQue.environments := by decide
theorem siQue_strategy : siQue.strategy = .polarityReversal := rfl

end Fragments.Spanish.PolarityMarking
