import Linglib.Core.Probability.Finite

/-!
# Bayesian Confirmation Measures on `PMF`
@cite{fitelson-1999} @cite{fitelson-2007} @cite{crupi-fitelson-tentori-2008}
@cite{edwards-1992} @cite{chung-mascarenhas-2024}

Confirmation-theoretic aggregates over a `PMF α`. Three pieces:

1. **Count-of-relevant-propositions** `countMeasure R`: the function
   `μ_R(w) = |{r ∈ R ∣ r(w)}|` of @cite{chung-mascarenhas-2024} (their eq. 7),
   as an `ℝ≥0∞`-valued function on worlds.

2. **Explanatory value** `sumLikelihoods p R φ = Σ_{e ∈ R} P(e ∣ φ)` —
   @cite{chung-mascarenhas-2024}'s aggregate (their eq. 12) in its
   directly-evaluable form.

3. **Difference and likelihood-ratio measures** (`differenceMeasure`,
   `likelihoodRatio`) from the @cite{fitelson-1999} plurality survey.

The headline bridge `condExpect_countMeasure_eq_sumLikelihoods` (C&M
eq. 12) says the conditional expectation of the *count* equals the sum
of likelihoods — exposing why "explanatory value" and "expected utility"
are the same operator with different `R`.

## Scope

The log-based likelihood-ratio `L(h, e) = log(P(e∣h)/P(e∣¬h))` is not
defined: `Real.log` on `ENNReal` ratios is `noncomputable` and not
`decide`-friendly. The un-logged `likelihoodRatio` is provided; log is
order-preserving so `>`/`<` claims transfer.

@cite{crupi-fitelson-tentori-2008}'s `Z`, Kemeny-Oppenheim `K`, and the
other measures from @cite{fitelson-1999} are not stocked here. Add them
when a Studies file actually consumes them.
-/

set_option autoImplicit false

namespace PMF.Confirmation

variable {α : Type*} [Fintype α]

open scoped ENNReal
open BigOperators Set

/-! ## §1. Count of relevant propositions (C&M's `μ_R`) -/

/-- `μ_R(a)` of @cite{chung-mascarenhas-2024}: the count of propositions
`r ∈ R` that are true at `a`. ENNReal-valued so it composes with PMF
arithmetic. Built on `Finset.filter` under `Classical.dec` since each
`r : Set α` is an arbitrary predicate without a free decidability
witness; consumers with decidable propositions get computability for
free at evaluation time. -/
noncomputable def countMeasure (R : Finset (Set α)) : α → ℝ≥0∞ := by
  classical
  exact fun a => (R.filter (a ∈ ·)).card

/-! ## §2. Explanatory value (C&M's sum of likelihoods) -/

/-- Sum of likelihoods over an evidence-set `R` given hypothesis `φ`:
`Σ_{e ∈ R} P(e ∣ φ)`. This is @cite{chung-mascarenhas-2024}'s
"explanatory value" in its directly-evaluable form (their eq. 12). -/
noncomputable def sumLikelihoods (p : PMF α) (R : Finset (Set α)) (φ : Set α) : ℝ≥0∞ :=
  ∑ e ∈ R, p.condProbSet φ e

/-! ## §3. Bayesian difference and likelihood-ratio measures -/

/-- The difference measure `D(h, e) = P(h ∣ e) − P(h)` of
@cite{fitelson-1999}. ℝ-valued because the subtraction would lose sign
under ENNReal's truncated subtraction. Negative values indicate that
`e` disconfirms `h`. Used by @cite{chung-mascarenhas-2024} §5 in the
plausibility-requirement discussion. -/
noncomputable def differenceMeasure (p : PMF α) (h e : Set α) : ℝ :=
  (p.condProbSet e h).toReal - (p.probOfSet h).toReal

/-- The un-logged likelihood-ratio `P(e ∣ h) / P(e ∣ ¬h)`. Equals `1` on
irrelevance, exceeds `1` on confirmation. @cite{fitelson-2007}'s `L` is
the log of this; we keep the ratio for `decide`-checkability. -/
noncomputable def likelihoodRatio (p : PMF α) (h e : Set α) : ℝ≥0∞ :=
  p.condProbSet h e / p.condProbSet hᶜ e

end PMF.Confirmation
