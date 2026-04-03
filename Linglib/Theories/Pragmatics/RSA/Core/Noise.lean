import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Linglib.Core.PropertyDomain

/-!
# Unified Noise Theory for RSA

@cite{waldon-degen-2021} @cite{kursat-degen-2021} @cite{giles-etal-2026}

This module provides a unified treatment of noise in RSA models.

## Noise Models in RSA

| Paper | Noise Type | Location |
|-------|-----------|----------|
| @cite{bergen-goodman-2015} | Channel | Transmission |
| @cite{degen-etal-2020} | Semantic | Perception |
| @cite{kursat-degen-2021} | Perceptual | Verification |
| @cite{giles-etal-2026} | Search efficiency | Psychophysics |

## Insight

All four use the same underlying operation:
```
noiseChannel(match, mismatch, b) = match * b + mismatch * (1 - b)
```

## Perceptual Grounding

@cite{giles-etal-2026} provide experimental evidence for the perceptual
grounding of noise parameters: discriminability (noise gap) is measured
via psychophysical staircases, connecting the abstract match/mismatch
parameters to observable perceptual thresholds. Their Exp 1 shows that
overinformativeness tracks discriminability × sufficiency across both
visual (colour) and auditory (material) modalities.

However, noise discrimination alone does not explain why colour is
disproportionately overinformed relative to other privileged features
like orientation (Exp 2). The residual colour privilege may reflect
the optimality of colour naming systems (@cite{regier-etal-2007},
@cite{zaslavsky-etal-2019}): colour categories are partitioned to
maximise perceptual discriminability, making colour inherently more
search-efficient than attributes whose category boundaries are not
perceptually optimised.

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
C = 1 - H(ε) -- for binary symmetric channel with error rate ε
```

-/

namespace RSA.Noise

-- The Unified Noise Channel

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

-- Basic Properties

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

-- Standard Noise Parameters

/-- Color parameters from @cite{degen-etal-2020}: low noise -/
def colorMatch : ℚ := 99/100
def colorMismatch : ℚ := 1/100
def colorDiscrimination : ℚ := colorMatch - colorMismatch  -- 0.98

/-- Size parameters from @cite{degen-etal-2020}: medium noise -/
def sizeMatch : ℚ := 8/10
def sizeMismatch : ℚ := 2/10
def sizeDiscrimination : ℚ := sizeMatch - sizeMismatch  -- 0.60

/-- Material parameters (HYPOTHETICAL, not from any paper): high noise.
    @cite{kursat-degen-2021} establishes the *ordering* (material harder
    than color) but not specific channel parameters. -/
def materialMatch : ℚ := 7/10
def materialMismatch : ℚ := 3/10
def materialDiscrimination : ℚ := materialMatch - materialMismatch  -- 0.40

/-- Orientation parameters: high discrimination (like colour).
    @cite{giles-etal-2026} Exp 2 confirms ≥99% labelling accuracy for
    orientation (vertical vs horizontal), comparable to colour. Orientation
    is a privileged visual feature (@cite{wolfe-horowitz-2017}) capable of
    producing pop-out effects and guiding pre-attentive search.

    Despite equal discrimination, colour is overinformed more than
    orientation — this dissociation is the key finding of Exp 2. -/
def orientationMatch : ℚ := 99/100
def orientationMismatch : ℚ := 1/100
def orientationDiscrimination : ℚ := orientationMatch - orientationMismatch  -- 0.98

-- Discrimination Ordering

/-- Color has higher discrimination than size -/
theorem color_gt_size : colorDiscrimination > sizeDiscrimination := by
  native_decide

/-- Size has higher discrimination than material -/
theorem size_gt_material : sizeDiscrimination > materialDiscrimination := by
  native_decide

/-- Colour and orientation have equal discrimination. -/
theorem color_eq_orientation :
    colorDiscrimination = orientationDiscrimination := by
  native_decide

/-- Full ordering: color = orientation > size > material -/
theorem discrimination_ordering :
    colorDiscrimination > sizeDiscrimination ∧
    sizeDiscrimination > materialDiscrimination :=
  ⟨color_gt_size, size_gt_material⟩

/-- The full ordering including orientation. -/
theorem discrimination_ordering_full :
    colorDiscrimination = orientationDiscrimination ∧
    colorDiscrimination > sizeDiscrimination ∧
    sizeDiscrimination > materialDiscrimination :=
  ⟨color_eq_orientation, color_gt_size, size_gt_material⟩

-- Perceptual Difficulty Connection

/-- Perceptual difficulty levels -/
inductive PerceptualDifficulty where
  | easy    -- Color-like, orientation-like
  | medium  -- Size-like
  | hard    -- Material-like
  deriving DecidableEq, Repr

/-- Map difficulty to discrimination -/
def difficultyToDiscrimination : PerceptualDifficulty → ℚ
  | .easy => colorDiscrimination
  | .medium => sizeDiscrimination
  | .hard => materialDiscrimination

/-- Easier perception → higher discrimination -/
theorem easier_higher_discrimination :
    difficultyToDiscrimination .easy > difficultyToDiscrimination .hard := by
  native_decide

-- ════════════════════════════════════════════════════
-- Colour Privilege: Limits of Noise-Based Prediction
-- ════════════════════════════════════════════════════

/-- The noise model predicts that attributes with equal discrimination
    should be overinformed at equal rates. Colour and orientation have
    equal noise discrimination (0.98), so the noise model predicts no
    preference between them.

    @cite{giles-etal-2026} Exp 2 falsifies this prediction: colour is
    overinformed significantly more than orientation (β = −0.97,
    95% CI = [−1.20, −0.75]) even when controlling for:
    - Perceptual discriminability (both ≥99% labelling accuracy)
    - Contextual distinctiveness (both equally salient)
    - Production effort (button-click equalises effort)
    - Word frequency (low-frequency colour terms tested)

    This means the noise model is *necessary but not sufficient*:
    discriminability drives overinformativeness (Exp 1), but something
    additional about colour — plausibly the perceptual optimality of
    colour category boundaries (@cite{regier-etal-2007}) — produces a
    residual privilege. -/
theorem noise_model_predicts_no_colour_orientation_difference :
    colorDiscrimination = orientationDiscrimination := by
  native_decide

/-- Product discrimination is monotone: when match scores are individually
    at least as large AND the gap is at least as large, the weighted
    product is at least as large.

    The gap condition alone is insufficient — counterexample:
    match₁=0, match₂=10, mismatch₁=0, mismatch₂=11, sizeMatch=100, sizeMismatch=1.
    Gap: 0 ≥ -1 ✓, but 0·100-0·1=0 < 10·100-11·1=989. -/
theorem product_discrimination_monotone
    (match₁ mismatch₁ match₂ mismatch₂ : ℚ)
    (sizeMatch sizeMismatch : ℚ)
    (h_gap : match₁ - mismatch₁ ≥ match₂ - mismatch₂)
    (h_match_mono : match₁ ≥ match₂)
    (h_size_nonneg : sizeMatch ≥ 0 ∧ sizeMismatch ≥ 0)
    (h_size_order : sizeMatch ≥ sizeMismatch) :
    match₁ * sizeMatch - mismatch₁ * sizeMismatch ≥
    match₂ * sizeMatch - mismatch₂ * sizeMismatch := by
  have key : match₁ * sizeMatch - mismatch₁ * sizeMismatch -
      (match₂ * sizeMatch - mismatch₂ * sizeMismatch) =
      (match₁ - match₂) * (sizeMatch - sizeMismatch) +
      ((match₁ - match₂) - (mismatch₁ - mismatch₂)) * sizeMismatch := by ring
  have h1 : (0 : ℚ) ≤ match₁ - match₂ := by linarith
  have h2 : (0 : ℚ) ≤ sizeMatch - sizeMismatch := by linarith
  have h3 : (0 : ℚ) ≤ (match₁ - match₂) - (mismatch₁ - mismatch₂) := by linarith
  have h_sum := add_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 h_size_nonneg.2)
  rw [← key] at h_sum
  linarith

end RSA.Noise

-- ════════════════════════════════════════════════════
-- PropertyDomain → Noise Parameters
-- ════════════════════════════════════════════════════

/-- Map a `PropertyDomain` to its established noise discrimination value.
    Returns `none` for domains without empirically grounded noise params. -/
def Core.PropertyDomain.noiseDiscrimination : Core.PropertyDomain → Option ℚ
  | .color       => some RSA.Noise.colorDiscrimination       -- 0.98
  | .orientation => some RSA.Noise.orientationDiscrimination  -- 0.98
  | .size        => some RSA.Noise.sizeDiscrimination         -- 0.60
  | .material    => some RSA.Noise.materialDiscrimination     -- 0.40
  | _            => none
