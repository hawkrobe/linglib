/-
# Unified SDS Constraint System

This module defines the core abstraction for Situation Description Systems (SDS)
as constraint combination systems. The key insight is that many linguistic phenomena
share a common structure:

1. A **parameter space** (thresholds, concepts, lexica) being marginalized over
2. A **selectional factor**: entity-dependent constraint
3. A **scenario factor**: context-dependent constraint
4. **Combination** via Product of Experts (multiplicative)

## Connection to Core.ProductOfExperts

This module is conceptually related to `Core.ProductOfExperts.FactoredDist`,
but provides a typeclass-based interface for more flexible instantiation.
The underlying math is the same: Product of Experts combination.

## Examples of SDS-style Systems

| Domain | Parameter | Selectional | Scenario |
|--------|-----------|-------------|----------|
| Gradable adjectives | threshold θ | P(θ yields true \| measure(x)) | P(θ \| context) |
| Generics | prevalence θ | P(θ yields true \| actual prevalence) | P(θ \| property type) |
| Concept disambiguation | concept c | P(c \| selectional role) | P(c \| scenario/frame) |
| LU-RSA | lexicon L | P(L \| compositional constraints) | P(L \| prior) |

## References

- Erk, K. & Herbelot, A. (2024). How to Marry a Star. Journal of Semantics.
- Bergen, L., Levy, R. & Goodman, N.D. (2016). Pragmatic reasoning through
  semantic inference. Semantics & Pragmatics.
- Lassiter, D. & Goodman, N.D. (2017). Adjectival vagueness in a Bayesian model.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

namespace SDS.Core

-- ============================================================================
-- Core Typeclass: SDSConstraintSystem
-- ============================================================================

/--
A constraint system in the style of Situation Description Systems (SDS).

The core pattern: given an entity and context, we marginalize over a parameter
space, combining selectional (entity-dependent) and scenario (context-dependent)
factors via Product of Experts.

## Type Parameters

- `α`: The system type (e.g., `GradableAdjective E`, `Concept`)
- `Θ`: The parameter space being marginalized over

## Fields

- `paramSupport`: Finite support for marginalization
- `selectionalFactor`: Entity-dependent factor P(θ | entity features)
- `scenarioFactor`: Context-dependent factor P(θ | scenario/frame)

## Key Operations

The unnormalized posterior at parameter θ is:
```
posterior(θ) = selectionalFactor(θ) × scenarioFactor(θ)
```

The normalized posterior divides by the sum over all θ in support.
-/
class SDSConstraintSystem (α : Type*) (Θ : outParam Type*) where
  /-- Support for the parameter space (for finite marginalization) -/
  paramSupport : α → List Θ
  /-- The selectional component: entity-dependent factor -/
  selectionalFactor : α → Θ → ℚ
  /-- The scenario component: context-dependent factor -/
  scenarioFactor : α → Θ → ℚ

namespace SDSConstraintSystem

variable {α Θ : Type*} [SDSConstraintSystem α Θ]

-- ============================================================================
-- Core Operations
-- ============================================================================

/--
Unnormalized posterior at a given parameter value.

This is the Product of Experts combination:
`posterior(θ) = selectionalFactor(θ) × scenarioFactor(θ)`
-/
def unnormalizedPosterior (sys : α) (θ : Θ) : ℚ :=
  selectionalFactor sys θ * scenarioFactor sys θ

/--
Partition function (normalizing constant) for the posterior.

`Z = Σ_θ selectionalFactor(θ) × scenarioFactor(θ)`
-/
def partitionFunction (sys : α) : ℚ :=
  (paramSupport sys).foldl (fun acc θ => acc + unnormalizedPosterior sys θ) 0

/--
Normalized posterior probability at a given parameter value.

`P(θ | sys) = unnormalizedPosterior(θ) / Z`

Returns 0 if Z = 0 (degenerate case).
-/
def normalizedPosterior (sys : α) (θ : Θ) : ℚ :=
  let Z := partitionFunction sys
  if Z = 0 then 0 else unnormalizedPosterior sys θ / Z

/--
Expected value of a function under the normalized posterior.

`E[f] = Σ_θ P(θ | sys) × f(θ)`
-/
def expectation (sys : α) (f : Θ → ℚ) : ℚ :=
  (paramSupport sys).foldl (fun acc θ => acc + normalizedPosterior sys θ * f θ) 0

/--
Probability that a predicate holds under the posterior.

`P(pred) = E[1_pred]`
-/
def posteriorProb (sys : α) (pred : Θ → Bool) : ℚ :=
  expectation sys fun θ => if pred θ then 1 else 0

-- ============================================================================
-- Properties
-- ============================================================================

/--
Product of Experts is commutative: order of factors doesn't matter.
-/
theorem poe_commutative (sys : α) (θ : Θ) :
    selectionalFactor sys θ * scenarioFactor sys θ =
    scenarioFactor sys θ * selectionalFactor sys θ := by
  ring

/--
Zero-absorbing: if either factor is zero, the posterior is zero.
-/
theorem poe_zero_selectional (sys : α) (θ : Θ)
    (h : selectionalFactor sys θ = 0) :
    unnormalizedPosterior sys θ = 0 := by
  simp only [unnormalizedPosterior, h, zero_mul]

theorem poe_zero_scenario (sys : α) (θ : Θ)
    (h : scenarioFactor sys θ = 0) :
    unnormalizedPosterior sys θ = 0 := by
  simp only [unnormalizedPosterior, h, mul_zero]

-- ============================================================================
-- Soft Meaning via Marginalization
-- ============================================================================

/--
Soft truth value: probability that a threshold-based predicate holds.

For threshold semantics, this computes:
`E[1_{measure(x) ≥ θ}]` under the posterior over θ

This is the key connection: threshold uncertainty yields soft/graded meanings.
-/
def softTruth (sys : α) (holds : Θ → Bool) : ℚ :=
  posteriorProb sys holds

/--
Marginal over parameter space.

Returns the distribution over some property computed from θ.
For SDS, this is how soft meanings emerge from Boolean semantics + uncertainty.
-/
def marginal (sys : α) (project : Θ → ℚ) : ℚ :=
  expectation sys project

end SDSConstraintSystem

-- ============================================================================
-- Conflict Detection
-- ============================================================================

/--
Find the element with maximum value according to a scoring function.
-/
def listArgmax {α : Type*} (xs : List α) (f : α → ℚ) : Option α :=
  xs.foldl (fun acc x =>
    match acc with
    | none => some x
    | some best => if f x > f best then some x else some best
  ) none

/--
Detect when selectional and scenario factors disagree.

A conflict occurs when the argmax of each factor differs.
This is useful for predicting ambiguity, puns, and zeugma.
-/
def hasConflict {α Θ : Type*} [SDSConstraintSystem α Θ] [BEq Θ]
    (sys : α) : Bool :=
  let support := SDSConstraintSystem.paramSupport sys
  let selMax := listArgmax support (SDSConstraintSystem.selectionalFactor sys)
  let scenMax := listArgmax support (SDSConstraintSystem.scenarioFactor sys)
  match selMax, scenMax with
  | some θ₁, some θ₂ => θ₁ != θ₂
  | _, _ => false

/--
Get the degree of conflict between factors.

Measures how different the expert preferences are.
-/
def conflictDegree {α Θ : Type*} [SDSConstraintSystem α Θ] [BEq Θ]
    (sys : α) : ℚ :=
  let support := SDSConstraintSystem.paramSupport sys
  let selMax := listArgmax support (SDSConstraintSystem.selectionalFactor sys)
  let scenMax := listArgmax support (SDSConstraintSystem.scenarioFactor sys)
  match selMax, scenMax with
  | some θ₁, some θ₂ =>
    if θ₁ == θ₂ then 0
    else
      let sel := SDSConstraintSystem.selectionalFactor sys
      let scen := SDSConstraintSystem.scenarioFactor sys
      |sel θ₁ - scen θ₁| + |sel θ₂ - scen θ₂|
  | _, _ => 0

-- ============================================================================
-- Degenerate Cases
-- ============================================================================

/--
A degenerate SDS where the scenario factor is uniform (no context dependence).

This captures cases like gradable nouns where the threshold is compositionally
determined rather than contextually inferred.
-/
def trivialScenario {α Θ : Type*} [SDSConstraintSystem α Θ]
    (sys : α) (θ : Θ) : Bool :=
  decide (SDSConstraintSystem.scenarioFactor sys θ = 1)

/--
Check if all scenario factors are trivial (constant 1).
-/
def hasUniformScenario {α Θ : Type*} [SDSConstraintSystem α Θ] (sys : α) : Bool :=
  (SDSConstraintSystem.paramSupport sys).all (trivialScenario sys)

-- ============================================================================
-- Connection to ProductOfExperts.FactoredDist
-- ============================================================================

/-!
## Relationship to Core.ProductOfExperts

The `SDSConstraintSystem` typeclass is conceptually equivalent to
`Core.ProductOfExperts.FactoredDist`, but with key differences:

1. **Typeclass vs Structure**: SDS uses a typeclass for instance inference,
   allowing automatic derivation of operations for any type that provides
   the selectional/scenario factors.

2. **Universe Polymorphism**: SDS is fully universe-polymorphic (`Type*`),
   while FactoredDist uses `Type`.

3. **Instance Pattern**: SDS supports instantiation at different entity types
   (e.g., `SDSConstraintSystem (AdjWithEntity E) ℚ` for any `E`).

For types where both apply, the underlying computation is identical:
- `unnormalizedPosterior = FactoredDist.unnormScores`
- `normalizedPosterior = FactoredDist.combine`
- `hasConflict` uses the same argmax-based detection

See `Core.ProductOfExperts` for the standalone PoE combinators.
-/

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## Summary

This module provides:

### Core Typeclass
- `SDSConstraintSystem α Θ`: Any domain with factored constraints over parameters

### Operations
- `unnormalizedPosterior`: Product of Experts combination
- `normalizedPosterior`: Normalized distribution over parameters
- `expectation`: Expected value under posterior
- `softTruth`: Soft meaning via marginalization

### Utilities
- `hasConflict`: Detect when factors disagree (predicts ambiguity)
- `conflictDegree`: Quantify disagreement between factors
- `hasUniformScenario`: Check for degenerate/trivial scenario factors

### Key Insight

SDS unifies many linguistic phenomena under a common computational pattern:
- Gradable adjectives (threshold uncertainty)
- Generics (prevalence threshold uncertainty)
- Concept disambiguation (concept uncertainty)
- Lexical uncertainty RSA (lexicon uncertainty)

All share: **Boolean semantics + parameter uncertainty = soft/graded meanings**
-/

end SDS.Core
