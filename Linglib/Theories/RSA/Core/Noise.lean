/-
# Unified Noise Theory for RSA

This module provides a unified treatment of noise in RSA models.

## Noise Models in RSA

| Paper | Noise Type | Location |
|-------|-----------|----------|
| Bergen & Goodman 2015 | Channel | Transmission |
| Degen et al. 2020 | Semantic | Perception |
| Kursat & Degen 2021 | Perceptual | Verification |

## Key Insight

All three use the same underlying operation:
```
noiseChannel(match, mismatch, b) = match * b + mismatch * (1 - b)
```

## Current Status: Shallow Integration

Currently, implementations import this module but don't deeply integrate:
- Proofs still unfold definitions manually rather than using shared lemmas
- No common typeclass that implementations instantiate
- Theorems must be re-proven in each implementation

## Future Work: Deep Integration

Proper integration would involve:

### 1. Typeclass for Noisy Semantics
```lean
class NoisySemantics (U W : Type) where
  φ : U → W → ℚ
  noiseParams : FeatureType → NoiseParams
  φ_decomposition : φ u w = Π features, noiseChannel (noiseParams f) (booleanMatch f u w)
```

### 2. Generic Theorems
```lean
theorem discrimination_from_params [NoisySemantics U W] (f : FeatureType) :
    featureDiscrimination f = (noiseParams f).discrimination
```

### 3. Automatic Instantiation
```lean
instance : NoisySemantics ReferringExpression Object := DegenSemantics
instance : NoisySemantics Utterance Meaning := BergenSemantics

-- Theorems apply to both automatically
#check @discrimination_from_params _ _ DegenSemantics
```

### 4. Information-Theoretic Measures
The current "discrimination" measure (match - mismatch) is a proxy for
informativeness but not actual mutual information I(X;Y). A proper
treatment would compute channel capacity:
```
C = 1 - H(ε)  -- for binary symmetric channel with error rate ε
```

## References

- Bergen & Goodman (2015). The Strategic Use of Noise.
- Degen et al. (2020). When redundancy is useful.
- Kursat & Degen (2021). Perceptual difficulty differences.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

namespace RSA.Noise

-- ============================================================================
-- The Unified Noise Channel
-- ============================================================================

/--
The fundamental noise channel operation.

Transforms Boolean `b ∈ {0, 1}` into graded value in [mismatch, match].
-/
def noiseChannel (onMatch onMismatch : ℚ) (b : ℚ) : ℚ :=
  onMatch * b + onMismatch * (1 - b)

/--
The noise gap measures discrimination power.
-/
def noiseGap (onMatch onMismatch : ℚ) : ℚ := onMatch - onMismatch

-- ============================================================================
-- Basic Properties
-- ============================================================================

@[simp]
theorem noiseChannel_one (onMatch onMismatch : ℚ) :
    noiseChannel onMatch onMismatch 1 = onMatch := by
  simp only [noiseChannel]; ring

@[simp]
theorem noiseChannel_zero (onMatch onMismatch : ℚ) :
    noiseChannel onMatch onMismatch 0 = onMismatch := by
  simp only [noiseChannel]; ring

theorem noiseChannel_discrimination (onMatch onMismatch : ℚ) :
    noiseChannel onMatch onMismatch 1 - noiseChannel onMatch onMismatch 0 =
    noiseGap onMatch onMismatch := by
  simp [noiseGap]

-- ============================================================================
-- Standard Noise Parameters
-- ============================================================================

/-- Color parameters from Degen et al. (2020): low noise -/
def colorMatch : ℚ := 99/100
def colorMismatch : ℚ := 1/100
def colorDiscrimination : ℚ := colorMatch - colorMismatch  -- 0.98

/-- Size parameters from Degen et al. (2020): medium noise -/
def sizeMatch : ℚ := 8/10
def sizeMismatch : ℚ := 2/10
def sizeDiscrimination : ℚ := sizeMatch - sizeMismatch  -- 0.60

/-- Material parameters (hypothetical from Kursat & Degen 2021): high noise -/
def materialMatch : ℚ := 7/10
def materialMismatch : ℚ := 3/10
def materialDiscrimination : ℚ := materialMatch - materialMismatch  -- 0.40

-- ============================================================================
-- Discrimination Ordering
-- ============================================================================

/-- Color has higher discrimination than size -/
theorem color_gt_size : colorDiscrimination > sizeDiscrimination := by
  native_decide

/-- Size has higher discrimination than material -/
theorem size_gt_material : sizeDiscrimination > materialDiscrimination := by
  native_decide

/-- Full ordering: color > size > material -/
theorem discrimination_ordering :
    colorDiscrimination > sizeDiscrimination ∧
    sizeDiscrimination > materialDiscrimination :=
  ⟨color_gt_size, size_gt_material⟩

-- ============================================================================
-- Perceptual Difficulty Connection
-- ============================================================================

/-- Perceptual difficulty levels -/
inductive PerceptualDifficulty where
  | easy    -- Color-like
  | medium  -- Size-like
  | hard    -- Material-like
  deriving DecidableEq, BEq, Repr

/-- Map difficulty to discrimination -/
def difficultyToDiscrimination : PerceptualDifficulty → ℚ
  | .easy => colorDiscrimination
  | .medium => sizeDiscrimination
  | .hard => materialDiscrimination

/-- Easier perception → higher discrimination -/
theorem easier_higher_discrimination :
    difficultyToDiscrimination .easy > difficultyToDiscrimination .hard := by
  native_decide

end RSA.Noise
