/-
# Kursat & Degen (2021): Perceptual Difficulty and Redundant Modification

"Perceptual difficulty differences predict asymmetry in redundant modification
with color and material adjectives"
Proceedings of the Linguistic Society of America 6(1): 676-688.

## Key Question

What is the SOURCE of the noise parameter in Degen et al. (2020)'s RSA model?

## The Perceptual Difficulty Hypothesis

The noise term reflects the **perceptual difficulty** of establishing whether
the property denoted by the adjective holds of the contextually relevant objects.

Prediction: More difficult to perceive → higher noise → less redundant use

## Experiments

1. **Exp 1**: Timed forced-choice property verification (color vs material)
2. **Exp 2**: Reference game measuring redundant modifier production
3. **Exp 3**: Perceptual difficulty in context (replication)

## Main Finding

Material adjectives are:
- Harder to perceive (higher RT, more errors)
- Less likely to be used redundantly

This supports the hypothesis that Degen et al.'s noise parameter
reflects perceptual difficulty.

## References

Kursat, L. & Degen, J. (2021). Perceptual difficulty differences predict
asymmetry in redundant modification with color and material adjectives.
Proc Ling Soc Amer 6(1). 676-688.
-/

import Linglib.Phenomena.Core.Basic
import Linglib.Theories.RSA.Core.Noise

namespace Phenomena.KursatDegen2021

open RSA.Noise

-- Property Types

/-- Property types tested in the experiments -/
inductive PropertyType where
  | color     -- e.g., "green", "blue"
  | material  -- e.g., "plastic", "metal", "wooden"
  | size      -- e.g., "small", "large" (from Degen et al. 2020)
  deriving DecidableEq, BEq, Repr

-- Experiment 1: Perceptual Difficulty Norms

/--
Perceptual difficulty datum from Exp 1.

Participants saw images with adjectives and indicated yes/no
as quickly as possible (4 second timeout).
-/
structure PerceptualDifficultyDatum where
  /-- The property type -/
  property : PropertyType
  /-- Mean proportion of correct responses -/
  accuracy : Float
  /-- Mean response time for correct responses (ms) -/
  responseTime : Float
  /-- Standard error for accuracy -/
  accuracySE : Float := 0
  /-- Standard error for RT -/
  rtSE : Float := 0
  /-- Notes -/
  notes : String := ""
  deriving Repr

/-- Exp 1 results: Color is easier to perceive than material -/
def exp1_color : PerceptualDifficultyDatum := {
  property := .color
  accuracy := 0.95      -- ~95% accuracy (estimated from Figure 2a)
  responseTime := 650   -- ~650ms (estimated from Figure 2b)
  notes := "Color adjectives: low error rates, fast responses"
}

def exp1_material : PerceptualDifficultyDatum := {
  property := .material
  accuracy := 0.80      -- ~80% accuracy (estimated from Figure 2a)
  responseTime := 950   -- ~950ms (estimated from Figure 2b)
  notes := "Material adjectives: higher error rates, slower responses"
}

/-- Statistical results from Exp 1 -/
structure Exp1Stats where
  /-- Log odds of error for material vs color -/
  errorBeta : Float := 0.48
  errorSE : Float := 0.12
  errorP : String := "p < .0001"
  /-- RT difference (material - color) -/
  rtBeta : Float := 5.44
  rtSE : Float := 4.74
  rtT : Float := 11.49
  rtP : String := "p < .0001"
  deriving Repr

def exp1_stats : Exp1Stats := {}

-- Experiment 2: Redundant Modifier Production

/--
Production datum from Exp 2.

Interactive reference game where speakers describe targets to listeners.
-/
structure ProductionDatum where
  /-- Which property was redundant (not needed for unique reference) -/
  redundantProperty : PropertyType
  /-- Proportion of utterances including the redundant property -/
  redundantUseRate : Float
  /-- Notes -/
  notes : String := ""
  deriving Repr

/-- Exp 2: Color is used redundantly more often than material -/
def exp2_colorRedundant : ProductionDatum := {
  redundantProperty := .color
  redundantUseRate := 0.75  -- ~75% redundant color use (from Figure 5)
  notes := "When color was redundant, speakers still mentioned it 75% of time"
}

def exp2_materialRedundant : ProductionDatum := {
  redundantProperty := .material
  redundantUseRate := 0.25  -- ~25% redundant material use (from Figure 5)
  notes := "When material was redundant, speakers mentioned it only 25% of time"
}

/-- Statistical results from Exp 2 -/
structure Exp2Stats where
  /-- Effect of redundant property (material vs color) on redundant use -/
  beta : Float := 2.32
  se : Float := 0.64
  p : String := "p < .0001"
  deriving Repr

def exp2_stats : Exp2Stats := {}

-- Experiment 3: Perceptual Difficulty in Context

/-- Exp 3 results: Replication with displays from Exp 2 -/
def exp3_color : PerceptualDifficultyDatum := {
  property := .color
  accuracy := 0.92      -- ~92% accuracy (estimated from Figure 7a)
  responseTime := 1100  -- ~1100ms (estimated from Figure 7b)
  notes := "Color in context: still easier than material"
}

def exp3_material : PerceptualDifficultyDatum := {
  property := .material
  accuracy := 0.78      -- ~78% accuracy (estimated from Figure 7a)
  responseTime := 2200  -- ~2200ms (estimated from Figure 7b)
  notes := "Material in context: still harder than color"
}

/-- Statistical results from Exp 3 -/
structure Exp3Stats where
  /-- Log odds of error for material vs color -/
  errorBeta : Float := 0.96
  errorSE : Float := 0.09
  errorP : String := "p < .0001"
  /-- RT difference (log-transformed) -/
  rtBeta : Float := 0.24
  rtSE : Float := 0.018
  rtT : Float := -59.62
  rtP : String := "p < .0001"
  deriving Repr

def exp3_stats : Exp3Stats := {}

-- The Perceptual Difficulty Hypothesis

/-!
## The Perceptual Difficulty Hypothesis

**Claim**: The noise parameter in Degen et al. (2020)'s RSA model reflects
the perceptual difficulty of property verification.

### Formalization

In our noise channel formalization:
- `noiseChannel onMatch onMismatch b = onMatch * b + onMismatch * (1 - b)`
- Discrimination = `onMatch - onMismatch`

The Perceptual Difficulty Hypothesis states:
- Higher perceptual difficulty → Lower discrimination
- Lower discrimination → Less redundant use

### Evidence

| Property | Perceptual Difficulty | Discrimination | Redundant Use |
|----------|----------------------|----------------|---------------|
| Color    | Low (fast, accurate) | High (~0.98)   | High (~75%)   |
| Size     | Medium               | Medium (~0.60) | Medium        |
| Material | High (slow, errors)  | Low            | Low (~25%)    |

### Theoretical Import

This gives an **empirical grounding** to the noise parameter:
- It's not just a free parameter to fit data
- It reflects measurable perceptual properties
- Different features have different inherent discriminability

### Connection to Information Theory

Perceptual difficulty → Channel capacity:
- Easy features (color): high channel capacity, low noise
- Hard features (material): low channel capacity, high noise

This connects to Bergen & Goodman's (2015) channel noise model.
-/

/-- Summary of the perceptual difficulty hypothesis -/
structure PerceptualDifficultyHypothesis where
  /-- Claim: noise reflects perceptual difficulty -/
  claim : String :=
    "The noise term in cs-RSA reflects perceptual difficulty of property verification"
  /-- Prediction -/
  prediction : String :=
    "More perceptually difficult properties are used redundantly less often"
  /-- Weak version: between-property effects -/
  weakVersion : String :=
    "Color vs material asymmetry explained by perceptual difficulty asymmetry"
  /-- Strong version: within-property effects -/
  strongVersion : String :=
    "Within property type, easier items used redundantly more often"
  /-- Evidence for weak version -/
  weakEvidence : Bool := true
  /-- Evidence for strong version -/
  strongEvidence : Bool := false  -- Not found in this study
  deriving Repr

def hypothesis : PerceptualDifficultyHypothesis := {}

-- Collected Data

def perceptualDifficultyData : List PerceptualDifficultyDatum :=
  [exp1_color, exp1_material, exp3_color, exp3_material]

def productionData : List ProductionDatum :=
  [exp2_colorRedundant, exp2_materialRedundant]

-- Connection to Degen et al. (2020) Parameters

/-!
## Mapping to SemanticParams

Based on the perceptual difficulty findings, we can interpret
Degen et al.'s parameters as reflecting perceptual discriminability:

```lean
-- Color: high discriminability (low perceptual difficulty)
colorMatch := 99/100    -- 0.99
colorMismatch := 1/100  -- 0.01
-- Discrimination = 0.98

-- Size: medium discriminability
sizeMatch := 8/10       -- 0.80
sizeMismatch := 2/10    -- 0.20
-- Discrimination = 0.60

-- Material (hypothetical, based on Kursat & Degen):
materialMatch := 7/10   -- 0.70 (lower due to higher perceptual difficulty)
materialMismatch := 3/10 -- 0.30
-- Discrimination = 0.40
```

The ordering of discrimination:
  color (0.98) > size (0.60) > material (0.40)

matches the ordering of perceptual ease:
  color (fast, accurate) > size > material (slow, error-prone)

and the ordering of redundant use:
  color (75%) > size > material (25%)
-/

/-- Hypothetical material parameters based on perceptual difficulty findings -/
structure MaterialParams where
  materialMatch : Float := 0.70
  materialMismatch : Float := 0.30
  discrimination : Float := 0.40
  notes : String := "Hypothetical values based on Kursat & Degen (2021)"
  deriving Repr

def hypotheticalMaterialParams : MaterialParams := {}

-- Connection to Unified Noise Theory

/-!
## Connection to `RSA.Noise`

The perceptual difficulty findings map directly to the unified noise theory
in `Theories/RSA/Core/Noise.lean`.
-/

/-- Map our property types to discrimination values from RSA.Noise -/
def propertyToDiscrimination : PropertyType → ℚ
  | .color => RSA.Noise.colorDiscrimination
  | .size => RSA.Noise.sizeDiscrimination
  | .material => RSA.Noise.materialDiscrimination

/-- Verify discrimination ordering matches perceptual difficulty ordering -/
theorem discrimination_matches_difficulty :
    propertyToDiscrimination .color > propertyToDiscrimination .size ∧
    propertyToDiscrimination .size > propertyToDiscrimination .material := by
  exact RSA.Noise.discrimination_ordering

#check (propertyToDiscrimination .color : ℚ)    -- 98/100
#check (propertyToDiscrimination .size : ℚ)     -- 60/100
#check (propertyToDiscrimination .material : ℚ) -- 40/100

end Phenomena.KursatDegen2021
