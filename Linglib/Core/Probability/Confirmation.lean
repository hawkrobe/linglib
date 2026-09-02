import Linglib.Core.Probability.Finite

/-!
# Bayesian Confirmation Measures on `PMF`
[fitelson-1999] [fitelson-2007] [crupi-fitelson-tentori-2008]
[edwards-1992] [chung-mascarenhas-2023]

Confirmation-theoretic aggregates over a `PMF α`. Three pieces:

1. **Count-of-relevant-propositions** `countMeasure R`: the function
   `μ_R(w) = |{i ∣ w ∈ R i}|` of [chung-mascarenhas-2023], as an
   `ℝ≥0∞`-valued function on worlds. The relevant propositions come as an
   indexed family `R : ι → Set α`, not a `Finset (Set α)`: rules are counted
   as *items*, so extensionally coincident rules keep their multiplicity
   (C&M's miners ideals "1 miner saved, …, 10 miners saved" collapse to two
   distinct world-sets on the six-world scenario space, yet `μ_R` must count
   up to ten).

2. **Explanatory value** `sumLikelihoods p R φ = Σ_i P(R i ∣ φ)` —
   [chung-mascarenhas-2023]'s aggregate in its directly-evaluable
   form. `condExpect_countMeasure` is the identity
   `P.condExpect φ (countMeasure R) = sumLikelihoods P R φ` — C&M's
   "expected utility = explanatory value" claim (their sum-of-likelihoods
   display); `sumLikelihoods_uniformOfFintype` evaluates it as counting
   ratios under a uniform prior.

3. **Difference and likelihood-ratio measures** (`differenceMeasure`,
   `likelihoodRatio`) from the [fitelson-1999] plurality survey.

## Scope

The log-based likelihood-ratio `L(h, e) = log(P(e∣h)/P(e∣¬h))` is not
defined: `Real.log` on `ENNReal` ratios is `noncomputable` and not
`decide`-friendly. The un-logged `likelihoodRatio` is provided; log is
order-preserving so `>`/`<` claims transfer.

[crupi-fitelson-tentori-2008]'s `Z`, Kemeny-Oppenheim `K`, and the
other measures from [fitelson-1999] are not stocked here. Add them
when a Studies file actually consumes them.

Mathlib's heavy `MeasureTheory.condExp` is the general measure-theoretic
counterpart for the underlying conditional expectation; this file's
`Core.Probability.Finite.condExpect` is the lightweight finite-PMF
wrapper. See its docstring for the design rationale.
-/

namespace PMF.Confirmation

variable {α ι : Type*} [Fintype α] [Fintype ι]

open scoped ENNReal
open BigOperators Set

/-! ### Count of relevant propositions (C&M's `μ_R`) -/

/-- `μ_R(a)` of [chung-mascarenhas-2023]: the number of relevant propositions
`R i` true at `a`, as the sum of their indicators (the paper states both the
cardinality and the indicator-sum form and notes their equivalence).
ENNReal-valued so it composes with PMF arithmetic. -/
noncomputable def countMeasure (R : ι → Set α) : α → ℝ≥0∞ :=
  ∑ i, (R i).indicator 1

omit [Fintype α] in
/-- The cardinality form of `countMeasure`. Instance-parametric decidability
keeps the filter kernel-computable for `decide` at concrete scenarios. -/
theorem countMeasure_apply (R : ι → Set α) (a : α) [∀ i, Decidable (a ∈ R i)] :
    countMeasure R a = (Finset.univ.filter (a ∈ R ·)).card := by
  simp [countMeasure, Set.indicator_apply, Finset.sum_boole]

/-! ### Explanatory value (C&M's sum of likelihoods) -/

/-- Sum of likelihoods over a relevant-proposition family `R` given
hypothesis `φ`: `Σ_i P(R i ∣ φ)`. [chung-mascarenhas-2023]'s
"explanatory value" in its directly-evaluable form. -/
noncomputable def sumLikelihoods (p : PMF α) (R : ι → Set α) (φ : Set α) : ℝ≥0∞ :=
  ∑ i, p.condProbSet φ (R i)

/-- [chung-mascarenhas-2023]'s sum-of-likelihoods display: the conditional
expectation of `μ_R` — expected utility read deontically, explanatory value
read epistemically — is the sum of likelihoods. -/
theorem condExpect_countMeasure (p : PMF α) (R : ι → Set α) (φ : Set α) :
    p.condExpect φ (countMeasure R) = sumLikelihoods p R φ := by
  rw [countMeasure, condExpect_sum]
  exact Finset.sum_congr rfl fun i _ => p.condExpect_indicator φ (R i)

/-- Under a uniform prior, explanatory value evaluates as a sum of counting
ratios. -/
theorem sumLikelihoods_uniformOfFintype [Nonempty α] (R : ι → Set α) (φ : Set α)
    [DecidablePred (· ∈ φ)] [∀ i, DecidablePred (· ∈ (φ ∩ R i))] :
    sumLikelihoods (PMF.uniformOfFintype α) R φ
      = (∑ i, ((Finset.univ.filter (· ∈ φ ∩ R i)).card : ℝ≥0∞))
          / (Finset.univ.filter (· ∈ φ)).card := by
  rw [sumLikelihoods, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by
    rw [condProbSet_uniformOfFintype φ (R i), div_eq_mul_inv]

/-! ### Bayesian difference and likelihood-ratio measures -/

/-- The difference measure `D(h, e) = P(h ∣ e) − P(h)` of
[fitelson-1999]. ℝ-valued because the subtraction would lose sign
under ENNReal's truncated subtraction. Negative values indicate that
`e` disconfirms `h`. Used by [chung-mascarenhas-2023] §5 in the
plausibility-requirement discussion. -/
noncomputable def differenceMeasure (p : PMF α) (h e : Set α) : ℝ :=
  (p.condProbSet e h).toReal - (p.probOfSet h).toReal

/-- The un-logged likelihood-ratio `P(e ∣ h) / P(e ∣ ¬h)`. Equals `1` on
irrelevance, exceeds `1` on confirmation. [fitelson-2007]'s `L` is
the log of this; we keep the ratio for `decide`-checkability. -/
noncomputable def likelihoodRatio (p : PMF α) (h e : Set α) : ℝ≥0∞ :=
  p.condProbSet h e / p.condProbSet hᶜ e

end PMF.Confirmation
