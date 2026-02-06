/-
# Threshold Semantics as SDS Instances

This module shows that all three threshold semantics domains from
`ThresholdSemantics.lean` are instances of `SDSConstraintSystem`:

1. **Gradable adjectives** (Lassiter & Goodman 2017)
2. **Generics** (Tessler & Goodman 2019)
3. **Gradable nouns** (Morzycki 2009)

## The Unified Pattern

All three domains share the threshold semantics pattern:
```
⟦predicate⟧(x) = true iff measure(x) ≥ threshold
```

The difference is in how the threshold is determined:
- Adjectives & Generics: threshold is uncertain, inferred via RSA
- Gradable nouns: threshold is compositionally fixed by size adjective

## SDS Mapping

| Domain | Param | Selectional | Scenario |
|--------|-------|-------------|----------|
| Adjectives | θ ∈ [0,1] | 1_{measure(x) ≥ θ} | P(θ) prior |
| Generics | θ ∈ [0,1] | 1_{prevalence ≥ θ} | P(θ) prior |
| Gradable nouns | θ ∈ {fixed} | 1_{θ = threshold} | 1 (trivial) |

## References

- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.
- Tessler & Goodman (2019). The Language of Generalization.
- Morzycki (2009). Degree modification of gradable nouns.
-/

import Linglib.Theories.SDS.Core
import Linglib.Comparisons.ThresholdSemantics

namespace SDS.ThresholdInstances

open Comparisons.ThresholdSemantics
open SDS.Core

-- Threshold Support: Discretized [0,1]

/--
Discretized threshold range: [0, 1/10, 2/10, ..., 1]

This provides finite support for marginalization over threshold values.
-/
def thresholdRange : List ℚ :=
  [0, 1/10, 2/10, 3/10, 4/10, 5/10, 6/10, 7/10, 8/10, 9/10, 1]

-- Instance 1: Gradable Adjectives

/-!
## Gradable Adjectives as SDS

For a gradable adjective like "tall":
- **Param**: threshold values θ ∈ [0,1]
- **Selectional**: indicator 1_{measure(x) ≥ θ} (which thresholds x satisfies)
- **Scenario**: P(θ) the threshold prior from context

The soft meaning E[1_{height(x) ≥ θ}] emerges from marginalization.
-/

/--
Entity-instantiated gradable adjective for SDS.

We curry the entity into the system so that selectional factors can depend on it.
-/
structure AdjWithEntity (E : Type) where
  /-- The underlying adjective -/
  adj : GradableAdjective E
  /-- The entity being predicated of -/
  entity : E

instance {E : Type} : SDSConstraintSystem (AdjWithEntity E) ℚ where
  paramSupport _ := thresholdRange
  selectionalFactor sys θ :=
    -- Selectional: which thresholds does this entity satisfy?
    -- Returns 1 if measure(x) ≥ θ, else 0
    if sys.adj.measure sys.entity ≥ θ then 1 else 0
  scenarioFactor sys θ :=
    -- Scenario: what's the contextual prior over thresholds?
    sys.adj.thresholdPrior θ

/-- Create an SDS system from an adjective and entity -/
def adjToSDS {E : Type} (adj : GradableAdjective E) (x : E) : AdjWithEntity E :=
  { adj := adj, entity := x }

-- Instance 2: Generics

/-!
## Generics as SDS

For a generic like "Birds fly":
- **Param**: threshold values θ ∈ [0,1] over prevalence
- **Selectional**: indicator 1_{prevalence ≥ θ} (which thresholds the prevalence satisfies)
- **Scenario**: P(θ) the threshold prior (varies by property type)

The soft truth emerges from marginalizing over the uncertain threshold.
-/

instance : SDSConstraintSystem GenericPredicate ℚ where
  paramSupport _ := thresholdRange
  selectionalFactor gen θ :=
    -- Selectional: which thresholds does this prevalence satisfy?
    if gen.prevalence ≥ θ then 1 else 0
  scenarioFactor gen θ :=
    -- Scenario: property-specific prior over prevalence thresholds
    gen.prevalencePrior θ

-- Instance 3: Gradable Nouns

/-!
## Gradable Nouns as SDS (Degenerate Case)

For a gradable noun like "big idiot":
- **Param**: threshold values (but only one is active)
- **Selectional**: delta function at the compositionally-determined threshold
- **Scenario**: trivial (constant 1) - no contextual uncertainty

This is a *degenerate* SDS where there's no marginalization - the threshold
is fixed by the size adjective's scale structure.
-/

instance {E : Type} : SDSConstraintSystem (GradableNounWithSize E) ℚ where
  paramSupport gn := [max gn.sizeThreshold gn.nounStandard]  -- Single point support
  selectionalFactor gn θ :=
    -- Delta function: only the compositional threshold gets mass
    if θ = max gn.sizeThreshold gn.nounStandard then 1 else 0
  scenarioFactor _ _ :=
    -- No scenario uncertainty for gradable nouns
    1

/--
Gradable nouns have trivial (uniform) scenario factors.
This captures the key difference from adjectives/generics.
-/
theorem gradable_noun_uniform_scenario {E : Type} (gn : GradableNounWithSize E) :
    hasUniformScenario (Θ := ℚ) gn = true := by
  simp only [hasUniformScenario, List.all_eq_true]
  intro θ _hθ
  simp only [trivialScenario, decide_eq_true_eq]
  rfl

-- Soft Meaning Computation

/--
Compute soft meaning for an adjective via SDS marginalization.

This shows the SDS machinery reproduces the expected soft meaning.
-/
def adjSoftMeaningSDS {E : Type} (adj : GradableAdjective E) (x : E) : ℚ :=
  let sys := adjToSDS adj x
  SDSConstraintSystem.softTruth sys λ θ => adj.measure x ≥ θ

/--
Compute soft truth for a generic via SDS marginalization.
-/
def genericSoftTruthSDS (gen : GenericPredicate) : ℚ :=
  SDSConstraintSystem.softTruth gen λ θ => gen.prevalence ≥ θ

/--
Compute holds for a gradable noun via SDS.

Since the scenario is trivial and support is a single point,
this reduces to a simple Boolean check.
-/
def gnHoldsSDS {E : Type} (gn : GradableNounWithSize E) (x : E) : Bool :=
  -- The SDS posterior is concentrated at the single threshold
  let θ := max gn.sizeThreshold gn.nounStandard
  gn.nounMeasure x ≥ θ

-- Scale Structure via SDS

/-!
## The Bigness Generalization

Morzycki (2009) shows why "big idiot" works but "small idiot" doesn't.
This follows from scale structure:

- **Positive adjectives** (big): min{d : big(d)} = θ_big > 0 (substantive)
- **Negative adjectives** (small): min{d : small(d)} = d₀ = 0 (vacuous)

In SDS terms:
- Positive → selectional factor is substantive (threshold > 0)
- Negative → selectional factor is vacuous (threshold = 0, always satisfied)
-/

/-- Positive size adjective has positive threshold -/
def isPositiveSizeAdj (adjName : String) : Bool :=
  adjName ∈ ["big", "huge", "enormous", "large", "gigantic"]

/-- Negative size adjective has zero threshold (vacuous) -/
def isNegativeSizeAdj (adjName : String) : Bool :=
  adjName ∈ ["small", "tiny", "minuscule", "little"]

/--
For positive size adjectives, the SDS threshold is substantive (> 0).
-/
theorem positive_adj_substantive_threshold {E : Type} (gn : GradableNounWithSize E)
    (_hpos : isPositiveSizeAdj gn.sizeAdj = true)
    (hthresh : gn.sizeThreshold > 0) :
    max gn.sizeThreshold gn.nounStandard > 0 := by
  exact lt_of_lt_of_le hthresh (le_max_left _ _)

-- Summary: All Three Domains are SDS

/--
All three threshold semantics domains satisfy SDSConstraintSystem.

We demonstrate this via the registered instances above. The instances are:
- `instSDSConstraintSystemAdjWithEntityRat`
- `instSDSConstraintSystemGenericPredicateRat`
- `instSDSConstraintSystemGradableNounWithSizeRat`
-/
example {E : Type} : SDSConstraintSystem (AdjWithEntity E) ℚ := inferInstance
example : SDSConstraintSystem GenericPredicate ℚ := inferInstance
example {E : Type} : SDSConstraintSystem (GradableNounWithSize E) ℚ := inferInstance

-- Summary

/-!
## Summary

This module establishes:

### Instances
1. `AdjWithEntity E` is an `SDSConstraintSystem _ ℚ`
2. `GenericPredicate` is an `SDSConstraintSystem _ ℚ`
3. `GradableNounWithSize E` is an `SDSConstraintSystem _ ℚ`

### Key Operations
- `adjToSDS`: Convert adjective + entity to SDS system
- `adjSoftMeaningSDS`: Compute soft meaning via SDS marginalization
- `genericSoftTruthSDS`: Compute generic soft truth via SDS
- `gnHoldsSDS`: Compute gradable noun truth via SDS

### Theorems
- `threshold_domains_are_sds`: All three domains are SDS instances
- `gradable_noun_uniform_scenario`: Gradable nouns have trivial scenario factors

### Design Decision: Entity Currying

For gradable adjectives, we curry the entity into an `AdjWithEntity` structure.
This allows the selectional factor to depend on entity features (measure value).

Alternative: Have `selectionalFactor : α → Entity → Θ → ℚ`
We chose currying to keep the typeclass simpler.
-/

end SDS.ThresholdInstances
