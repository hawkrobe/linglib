/-
# Unified Threshold Semantics

A comparison showing how threshold semantics appears across three domains:
1. **Gradable adjectives** (Lassiter & Goodman 2017)
2. **Generics/habituals** (Tessler & Goodman 2019)
3. **Gradable nouns** (Morzycki 2009)

## The Common Pattern

All three share:
```
⟦predicate⟧(x) = true iff measure(x) ≥ threshold
```

Where:
- **measure**: maps entities to degrees on a scale
- **threshold**: the cutoff for the predicate to apply

## Key Differences

| Domain | Scale | Threshold | Uncertainty |
|--------|-------|-----------|-------------|
| Adjectives | height(x) | θ_tall | RSA: inferred pragmatically |
| Generics | prevalence(F,K) | θ_gen | RSA: inferred pragmatically |
| Gradable nouns | degree(N,x) | min{d:big(d)} | Fixed by size adjective |

## The Bigness/Smallness Asymmetry

Morzycki (2009) shows why "big idiot" works but "small idiot" doesn't:
- For BIG: min{d : big(d)} = some positive threshold → substantive requirement
- For SMALL: min{d : small(d)} = d₀ (scale minimum) → vacuous!

This parallels the positive/negative adjective asymmetry in degree semantics.

## References

- Lassiter, D. & Goodman, N.D. (2017). Adjectival vagueness in a Bayesian model.
- Tessler, M.H. & Goodman, N.D. (2019). The Language of Generalization.
- Morzycki, M. (2009). Degree modification of gradable nouns.
- Kennedy, C. (2007). Vagueness and grammar.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

namespace Comparisons.ThresholdSemantics

-- ============================================================================
-- Abstract Threshold Predicate
-- ============================================================================

/-- The common structure across all three domains -/
structure ThresholdPredicate (Entity Degree : Type) [LE Degree] where
  /-- Name of the predicate -/
  name : String
  /-- Measure function: entity → degree -/
  measure : Entity → Degree
  /-- The threshold for the predicate to apply -/
  threshold : Degree

/-- Threshold semantics: predicate true iff measure ≥ threshold -/
def ThresholdPredicate.holds {E D : Type} [LE D] [DecidableRel (α := D) (· ≤ ·)]
    (p : ThresholdPredicate E D) (x : E) : Bool :=
  p.threshold ≤ p.measure x

-- ============================================================================
-- Domain 1: Gradable Adjectives (Lassiter & Goodman 2017)
-- ============================================================================

/-!
## Gradable Adjectives

⟦tall⟧(x, θ) = 1 iff height(x) > θ

The threshold θ is uncertain and inferred pragmatically via RSA.
Context-sensitivity emerges because the height prior varies by reference class.
-/

/-- Adjective as threshold predicate with uncertain threshold -/
structure GradableAdjective (Entity : Type) where
  name : String
  /-- The measure function (e.g., height) -/
  measure : Entity → ℚ
  /-- Prior over threshold values -/
  thresholdPrior : ℚ → ℚ

/-- Hard semantics at a fixed threshold -/
def GradableAdjective.meansAt {E : Type} (adj : GradableAdjective E) (θ : ℚ) (x : E) : Bool :=
  adj.measure x > θ

/-- Soft semantics: integrate over uniform θ gives measure value directly -/
def GradableAdjective.softMeaning {E : Type} (adj : GradableAdjective E) (x : E) : ℚ :=
  adj.measure x  -- P(random θ < measure(x)) = measure(x) for uniform θ on [0,1]

-- ============================================================================
-- Domain 2: Generics (Tessler & Goodman 2019)
-- ============================================================================

/-!
## Generics

⟦gen⟧(p, θ) = 1 iff prevalence p > threshold θ

Same structure as adjectives! The scale is prevalence (proportion of kind with property).
Prevalence priors (P(p)) vary by property, explaining judgment differences.
-/

/-- Generic as threshold predicate over prevalence -/
structure GenericPredicate where
  /-- The property being predicated -/
  property : String
  /-- The kind -/
  kind : String
  /-- Prevalence of property in kind -/
  prevalence : ℚ
  /-- Prior over prevalence values (property-specific) -/
  prevalencePrior : ℚ → ℚ

/-- Hard semantics at a fixed threshold -/
def GenericPredicate.trueAt (gen : GenericPredicate) (θ : ℚ) : Bool :=
  gen.prevalence > θ

/-- Soft semantics: ∫δ_{p>θ}dθ = p -/
def GenericPredicate.softTruth (gen : GenericPredicate) : ℚ :=
  gen.prevalence

-- ============================================================================
-- Domain 3: Gradable Nouns (Morzycki 2009)
-- ============================================================================

/-!
## Gradable Nouns

⟦big idiot⟧(x) = 1 iff idiot(x) ≥ min{d : big(d)} ∧ idiot(x) ≥ standard(idiot)

The threshold is determined by the SIZE ADJECTIVE, not pragmatic inference.
This is why "small idiot" fails: min{d : small(d)} = d₀ is always satisfied.
-/

/-- Gradable noun with size adjective modification -/
structure GradableNounWithSize (Entity : Type) where
  nounName : String
  /-- Measure function for the noun -/
  nounMeasure : Entity → ℚ
  /-- Standard for the noun (must be an N to be a big N) -/
  nounStandard : ℚ
  /-- Size adjective name -/
  sizeAdj : String
  /-- Threshold from size adjective: min{d : size(d)} -/
  sizeThreshold : ℚ

/-- Semantics: both size threshold and noun standard must be met -/
def GradableNounWithSize.holds {E : Type} (gn : GradableNounWithSize E) (x : E) : Bool :=
  gn.sizeThreshold ≤ gn.nounMeasure x ∧ gn.nounStandard ≤ gn.nounMeasure x

-- ============================================================================
-- The Unified View
-- ============================================================================

/-!
## Mapping to the Abstract Pattern

All three can be seen as instances of ThresholdPredicate:

1. **Adjective** "x is tall":
   - measure = height
   - threshold = inferred θ_tall

2. **Generic** "Ks are F":
   - measure = prevalence(F, K)
   - threshold = inferred θ_gen

3. **Gradable noun** "x is a big idiot":
   - measure = idiot
   - threshold = max(sizeThreshold, nounStandard)
-/

/-- Convert adjective to threshold predicate at a given θ -/
def adjToThreshold {E : Type} (adj : GradableAdjective E) (θ : ℚ) : ThresholdPredicate E ℚ :=
  { name := adj.name
  , measure := adj.measure
  , threshold := θ
  }

/-- Convert generic to threshold predicate at a given θ -/
def genericToThreshold (gen : GenericPredicate) (θ : ℚ) : ThresholdPredicate Unit ℚ :=
  { name := s!"{gen.kind} {gen.property}"
  , measure := fun _ => gen.prevalence
  , threshold := θ
  }

/-- Convert gradable noun to threshold predicate -/
def gnToThreshold {E : Type} (gn : GradableNounWithSize E) : ThresholdPredicate E ℚ :=
  { name := s!"{gn.sizeAdj} {gn.nounName}"
  , measure := gn.nounMeasure
  , threshold := max gn.sizeThreshold gn.nounStandard
  }

-- ============================================================================
-- Key Insight: Scale Structure Effects
-- ============================================================================

/-!
## Why Polarity Matters

The BIGNESS GENERALIZATION (Morzycki 2009):
- "big/huge/enormous N" ✓ has degree reading
- "small/tiny/minuscule N" ✗ no degree reading

**Explanation via scale structure:**

For positive adjectives (big):
- big(d) iff d ≥ θ_big (upward monotonic)
- min{d : big(d)} = θ_big (a substantive positive value)

For negative adjectives (small):
- small(d) iff d ≤ θ_small (downward monotonic)
- min{d : small(d)} = d₀ (the scale minimum, always satisfied!)

**This parallels other scale structure effects:**
- Measure phrases: "6 feet tall" ✓ vs "6 feet short" ✗
- Degree modification: "completely full" ✓ vs "completely tall" ✗
-/

/-- Positive (upward monotonic) size predicate -/
def positiveSizePred (threshold : ℚ) : ℚ → Bool :=
  fun d => threshold ≤ d

/-- Negative (downward monotonic) size predicate -/
def negativeSizePred (threshold : ℚ) : ℚ → Bool :=
  fun d => d ≤ threshold

/-- Min degree for positive predicate is the threshold itself -/
theorem min_positive (θ : ℚ) (hθ : 0 < θ) :
    ∃ d, positiveSizePred θ d ∧ ∀ d', positiveSizePred θ d' → d ≤ d' := by
  use θ
  refine ⟨?_, ?_⟩
  · -- positiveSizePred θ θ = true, i.e., θ ≤ θ
    simp only [positiveSizePred, decide_eq_true_eq]
    exact le_refl θ
  · intro d' hd'
    simp only [positiveSizePred, decide_eq_true_eq] at hd'
    exact hd'

/-- Min degree for negative predicate is 0 (the scale minimum)
    On a non-negative scale [0, ∞), 0 is always the minimum satisfying "small" -/
theorem min_negative (θ : ℚ) (hθ : 0 ≤ θ) :
    ∃ d, negativeSizePred θ d ∧ ∀ d', 0 ≤ d' → negativeSizePred θ d' → d ≤ d' := by
  use 0
  constructor
  · simp only [negativeSizePred, decide_eq_true_eq]
    exact hθ
  · intro d' hd' _
    exact hd'

-- ============================================================================
-- Summary: The Three Instantiations
-- ============================================================================

/-!
## Summary Table

| Paper | Domain | measure(x) | threshold | How θ determined |
|-------|--------|------------|-----------|------------------|
| Lassiter & Goodman 2017 | Adjectives | height, cost, etc. | θ_adj | Pragmatic inference (RSA) |
| Tessler & Goodman 2019 | Generics | prevalence(F,K) | θ_gen | Pragmatic inference (RSA) |
| Morzycki 2009 | Gradable nouns | noun-degree(x) | min{d:big(d)} | Size adjective scale structure |

## Shared Properties

1. **Measure functions**: All map entities to degrees on ordered scales
2. **Threshold comparison**: Truth requires exceeding a threshold
3. **Context sensitivity**: All show context-dependent interpretation
4. **Vagueness**: All involve borderline cases near the threshold

## Key Differences

1. **Threshold source**:
   - RSA models: θ is a latent variable, inferred pragmatically
   - Morzycki: θ is determined compositionally by size adjective

2. **Polarity effects**:
   - RSA models: both "tall" and "short" work (different θ)
   - Gradable nouns: only "big" works (scale structure constraint)

3. **Priors**:
   - Adjectives: prior over heights (reference class dependent)
   - Generics: prior over prevalence (property dependent)
   - Nouns: no prior needed (θ fixed by grammar)
-/

end Comparisons.ThresholdSemantics
