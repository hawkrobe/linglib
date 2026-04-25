import Linglib.Core.Lexical.NegMarker

/-! # Italian Negation Fragment
@cite{haspelmath-2013} @cite{dryer-2013-wals} @cite{zanuttini-1997} @cite{cinque-1999}

Italian sentential negation: the standard preverbal negation particle *non*
and its packaging as a `NegationSystem`. The marker is a free particle
in preverbal position; WALS Ch 143A classifies Italian as `.negv`.
Italian object clitics attach between *non* and the verb (*non lo vedo*,
not **lo non vedo*) — the canonical syntactic analysis is
@cite{zanuttini-1997}'s NegP cartography, refined by @cite{cinque-1999}'s
adverb hierarchy.

## Sibling files

Italian negation is distributed across four coordinated files. This file
holds only the operator (the marker + system). The other axes:

- `Fragments/Italian/PolarityItems.lean` — lexical reactives: n-words
  (*nessuno*, *niente*, *mai*, *neanche/nemmeno/neppure*), the formal NPI
  *alcuno*, the emphatic reinforcer *mica*, the FCIs *qualsiasi/qualunque*.
  The operator/lexical-reactive split is documented in
  `Core/Lexical/NegMarker.lean`.
- `Fragments/Italian/ExpletiveNegation.lean` — the 11 environments where
  *non* appears vacuously (Greco 2020): *temere/dubitare* complements,
  *prima che*, *a meno che*, comparative *quanto*, etc. Distinct axis from
  standard sentential negation.
- `Fragments/Italian/PolarityMarking.lean` — sentence-level polarity
  strategies (emphatic affirmation, focus particles).

Bias-conditioned *non₂* (the non-truth-functional comparative *non* of
Napoli & Nespor 1976) surfaces obliquely via the `pur` and `affatto`
entries in `PolarityItems.lean`.
-/

namespace Fragments.Italian.Negation

open Core.Lexical.NegMarker

/-- *non* — Italian's standard preverbal negation particle.
    `Non ho visto nessuno` 'NEG have seen nobody' = "I didn't see anyone".
    A free word, not a clitic; syntactically immediately preverbal. -/
def non : NegMarkerEntry :=
  { form := "non"
  , morphemeType := .particle
  , position := .preverbal }

/-- The Italian negation system: a single preverbal particle.
    The Fragment-side joint consumed by `Phenomena/Negation/Typology.lean`.
    WALS classifications are pulled from `Datasets/WALS/Features/F112A.lean`
    et al. via `NegationSystem.ofISO` — never hand-encoded. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "ita" [non]

end Fragments.Italian.Negation
