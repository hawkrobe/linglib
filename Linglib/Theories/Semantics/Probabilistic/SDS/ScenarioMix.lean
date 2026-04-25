import Linglib.Core.Probability.DirichletMultinomial
import Linglib.Core.Probability.PMFFin

/-!
# Scenario-mix marginal for SDS

The scenario-mix node at the top of the SDS graphical model
(@cite{erk-herbelot-2024} §5.1, Figure 5 node (1)) has *as its value* an
element of the simplex `Δ(Scenario)` — a distribution over scenarios.
Per-concept scenario nodes (Figure 5 nodes (2), (3), (4)) then draw
their value from this sampled distribution. The simplex-valued node is
governed by a Dirichlet(α) prior, with concentration parameter `α`
controlling sparsity: `α < 1` favors peaked mixtures (paper §5.1,
mechanism behind "utterances draw on coherent scenarios").

## Honest scope: count marginal, not the simplex node

Mathlib does not have the Dirichlet distribution over the simplex. This
file does **not** model paper Figure 5 node (1) directly. Instead it
provides the **count marginal**: by D-M conjugacy, the marginal joint
over (scenario assignments to `N` concept-nodes) — integrating out the
simplex — is a Dirichlet-Multinomial distribution over the integer
count vector. Live in `Core/Probability/DirichletMultinomial.lean` as
`DirichletMultinomial.pmf : PMF (α → ℕ)`.

This is enough to reproduce paper Tables 1–2 (the predictive at each
concept-node + the joint posterior given observations both factor
through the count marginal), but we do *not* expose a typed handle on
node (1)'s simplex value. Recovering simplex summaries from the count
marginal requires an inversion step that Phase 2 may or may not need.

## Dirichlet–Multinomial normalization (now proved)

`DirichletMultinomial.pmf` is built from `pmfReal_hasSum_one` — the
Dirichlet–Multinomial normalization theorem. As of 0.230.313 this is
fully proved (no sorries) via the chain:
`PolyaUrn.seqProb_succ` (Polya predictive recurrence via `Real.Gamma_add_one`)
→ `PolyaUrn.sum_seqProb_eq_one` (induction on N via `Fin.snocEquiv`)
→ `multinomCount_mul_prod_factorial` (multinomial counting)
→ `pmfReal_hasSum_one` (regrouping + ENNReal lift). The whole substrate
is sorry-free.

## Generic primitives live in `Core/Probability/PolyaUrn.lean`

The symmetric-urn constructor and the Polya predictive (`(α + counts s) /
(K · α + ∑ counts)`) are generic Polya-urn computations, not specific to
"scenarios" or to Erk-Herbelot. They live in `Core/Probability/PolyaUrn.lean`
as `PolyaUrn.symmetric` and `PolyaUrn.predictive`. This file's
`scenarioCountMarginal`/`scenarioCountPosterior` are paper-faithful
naming aliases over those primitives.

## API

- `scenarioCountMarginal α N` — the prior over scenario-assignment count
  vectors at `N` concept-nodes given symmetric Dirichlet(α, …, α).
  A `PMF (Scenario → ℕ)`.
- `scenarioCountPosterior α observed newDraws` — the posterior count
  marginal for `newDraws` *new* concept-node scenario assignments after
  observing `observed` counts. By D-M conjugacy, a Dirichlet-Multinomial
  with shifted Dirichlet parameters `α + observed`.
- For the closed-form predictive at the next single concept-node, use
  `(PolyaUrn.symmetric α hα).predictive counts s` directly from
  `Core/Probability/PolyaUrn.lean`.
-/

namespace Semantics.Probabilistic.SDS.ScenarioMix

open scoped ENNReal
open ProbabilityTheory

variable (Scenario : Type) [Fintype Scenario] [DecidableEq Scenario] [Nonempty Scenario]

/-- The scenario-count marginal: a `PMF` over scenario-assignment count
vectors at `N` concept-nodes, given symmetric Dirichlet(α) over scenarios.
Wraps `DirichletMultinomial.pmf (PolyaUrn.symmetric α hα)`. *Not* the
simplex-valued node (1) of paper Figure 5 — see file docstring "Honest
scope". -/
noncomputable def scenarioCountMarginal (α : ℝ) (hα : 0 < α) (N : ℕ) :
    PMF (Scenario → ℕ) :=
  DirichletMultinomial.pmf (PolyaUrn.symmetric (α := Scenario) α hα) N

variable {Scenario}

/-- The scenario-count posterior after observing scenario counts `observed`,
governing `newDraws` *additional* concept-node scenario assignments. By
D-M conjugacy, this is the Dirichlet-Multinomial with shifted Dirichlet
parameters `α + observed s` (asymmetric, no longer fully symmetric).

The substantive conjugacy claim — that this construction equals the
Bayesian posterior of `scenarioCountMarginal` given observations — is
not stated here because conditioning on observations requires the full
graphical model assembly (Phase 2). At Phase 1, the construction *is*
the conjugate posterior by the standard Dirichlet-Multinomial conjugacy,
which the type signature reflects (asymmetric pseudo-counts). -/
noncomputable def scenarioCountPosterior (α : ℝ) (hα : 0 < α)
    (observed : Scenario → ℕ) (newDraws : ℕ) : PMF (Scenario → ℕ) :=
  DirichletMultinomial.pmf
    { pseudo := fun s => α + observed s
      pseudo_pos := fun s => by positivity }
    newDraws

end Semantics.Probabilistic.SDS.ScenarioMix
