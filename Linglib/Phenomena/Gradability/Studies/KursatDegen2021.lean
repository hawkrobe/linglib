/-
# Kursat & Degen (2021): Perceptual Difficulty and Redundant Modification

Perceptual difficulty predicts redundant modifier use. Material adjectives are harder to perceive and less redundantly used than color adjectives.

## Main definitions

`PropertyType`, `PerceptualDifficultyDatum`, `ProductionDatum`, `Exp1Stats`, `Exp2Stats`, `Exp3Stats`, `PerceptualDifficultyHypothesis`

## References

- Kursat & Degen (2021)
-/

import Linglib.Phenomena.Core.Basic
import Linglib.Theories.RSA.Core.Noise

namespace Phenomena.KursatDegen2021

open RSA.Noise

-- Property Types

/-- Property type tested. -/
inductive PropertyType where
  | color
  | material
  | size
  deriving DecidableEq, BEq, Repr

-- Experiment 1: Perceptual Difficulty Norms

/-- Perceptual difficulty datum from Exp 1. -/
structure PerceptualDifficultyDatum where
  property : PropertyType
  accuracy : Float
  responseTime : Float
  accuracySE : Float := 0
  rtSE : Float := 0
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

/-- Production datum from Exp 2. -/
structure ProductionDatum where
  redundantProperty : PropertyType
  redundantUseRate : Float
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


/-- Perceptual difficulty hypothesis summary. -/
structure PerceptualDifficultyHypothesis where
  claim : String :=
    "The noise term in cs-RSA reflects perceptual difficulty of property verification"
  prediction : String :=
    "More perceptually difficult properties are used redundantly less often"
  weakVersion : String :=
    "Color vs material asymmetry explained by perceptual difficulty asymmetry"
  strongVersion : String :=
    "Within property type, easier items used redundantly more often"
  weakEvidence : Bool := true
  strongEvidence : Bool := false
  deriving Repr

def hypothesis : PerceptualDifficultyHypothesis := {}

-- Collected Data

def perceptualDifficultyData : List PerceptualDifficultyDatum :=
  [exp1_color, exp1_material, exp3_color, exp3_material]

def productionData : List ProductionDatum :=
  [exp2_colorRedundant, exp2_materialRedundant]


/-- Hypothetical material parameters based on perceptual difficulty findings -/
structure MaterialParams where
  materialMatch : Float := 0.70
  materialMismatch : Float := 0.30
  discrimination : Float := 0.40
  notes : String := "Hypothetical values based on Kursat & Degen (2021)"
  deriving Repr

def hypotheticalMaterialParams : MaterialParams := {}

/-- Map property types to discrimination values. -/
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
