import Linglib.Theories.Semantics.Conditionals.Counterfactual.QuantifierEmbedding

/-!
# Counterfactuals via implicature (Bassi & Bar-Lev)

@cite{bassi-bar-lev-2018}

@cite{bassi-bar-lev-2018} propose an alternative to the selectional
theory: counterfactuals have a basic EXISTENTIAL meaning (true if
some closest A-world satisfies B), strengthened to universal by an
exhaustivity operator (EXH). In mixed scenarios, EXH strengthening
fails, leaving the basic existential meaning.

Under this approach:
- Basic meaning: ∃w ∈ closest(w,A). B(w) — EXISTENTIAL
- Strengthened: ∀w ∈ closest(w,A). B(w) — UNIVERSAL (via EXH)
- In mixed scenarios: EXH fails → basic existential → ALL quantifiers
  get existential individual results

## Wrong Prediction

The implicature theory predicts that in mixed scenarios, all
quantified counterfactuals have the SAME (existential) individual
results. Since existential is always true when B holds for some
closest world:
- every(true) = true, some(true) = true, no(true) = false,
  not-every(true) = false

But @cite{ramotowska-marty-romoli-santorio-2025} observe:
- every = LOW (~1), some = HIGH (~97), no = LOW (~1),
  not-every = HIGH (~86)

The implicature theory gets "every" and "not-every" WRONG:
- Predicts: every = HIGH (∀d. true), but observed: every = LOW
- Predicts: not-every = LOW (¬∀d. true = false), but observed:
  not-every = HIGH

This file makes those wrong predictions formal as Lean theorems
that can be cited (in the contrastive direction) by the
@cite{ramotowska-marty-romoli-santorio-2025} study file.
-/

namespace Semantics.Conditionals.Counterfactual

open Core.Duality (Truth3)

/-- Under the implicature approach with all-true individual results,
    "every" is predicted true — the OPPOSITE of the observed data
    (~1.5/99). The implicature theory predicts "every" = TRUE because
    individual CFs are all existentially true, and conjunctive
    projection of all-true = true.

    This contradicts @cite{ramotowska-marty-romoli-santorio-2025}: the
    selectional theory correctly predicts "every" = FALSE via
    conjunctive projection over mixed (not uniformly true) individual
    results. -/
theorem implicature_wrong_for_every :
    projectTruthValues .conjunctive [Truth3.true, Truth3.true] = .true := by
  decide

/-- Implicature predicts "not-every" = FALSE (since not-every(all-true)
    = ∃d.¬true = false). This contradicts the observed data
    (not-every ≈ 86/99). The discriminating case alongside
    `implicature_wrong_for_every`. -/
theorem implicature_wrong_for_notEvery :
    projectTruthValues .disjunctive
      ([Truth3.true, Truth3.true].map Truth3.neg) = .false := by
  decide

end Semantics.Conditionals.Counterfactual
