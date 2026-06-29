import Mathlib.Data.Rat.Defs
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Linglib.Features.PropertyDomain

/-!
# Unified Noise Theory for RSA

[waldon-degen-2021] [kursat-degen-2021] [giles-etal-2026]

This module provides a unified treatment of noise in RSA models.

## Noise Models in RSA

| Paper | Noise Type | Location |
|-------|-----------|----------|
| [bergen-goodman-2015] | Channel | Transmission |
| [degen-etal-2020] | Semantic | Perception |
| [kursat-degen-2021] | Perceptual | Verification |
| [giles-etal-2026] | Search efficiency | Psychophysics |

## Insight

All four use the same underlying operation:
```
noiseChannel(match, mismatch, b) = match * b + mismatch * (1 - b)
```

## Perceptual Grounding

[giles-etal-2026] provide experimental evidence for the perceptual
grounding of noise parameters: discriminability (noise gap) is measured
via psychophysical staircases, connecting the abstract match/mismatch
parameters to observable perceptual thresholds. Their Exp 1 shows that
overinformativeness tracks discriminability × sufficiency across both
visual (colour) and auditory (material) modalities.

However, noise discrimination alone does not explain why colour is
disproportionately overinformed relative to other privileged features
like orientation (Exp 2). The residual colour privilege may reflect
the optimality of colour naming systems ([regier-etal-2007],
[zaslavsky-etal-2019]): colour categories are partitioned to
maximise perceptual discriminability, making colour inherently more
search-efficient than attributes whose category boundaries are not
perceptually optimised.

## Bundles using this primitive

The `noiseChannel` operation is the per-feature primitive consumed by
*structure-shaped* bundles, not a typeclass. Every paper picks its own
reliability parameters, so there is no canonical `NoisySemantics` instance
per `(U, W)` pair — each study constructs an explicit value of one of:

- `RSA.NoisyLex` (`Noisy.lean`) — Product-of-Experts noisy semantics
  ([degen-etal-2020], [waldon-degen-2021],
  [schlotterbeck-wang-2023]). PoE prefix product via
  `RSA.prefixMeaning` (`Sequential.lean`).
- `RSA.IncrementalSemantics` (`Incremental.lean`) — extension-counting
  Boolean semantics ([cohn-gordon-goodman-potts-2019]).

Information-theoretic refinement (channel capacity `C = 1 - H(ε)` for
binary symmetric channels) is a future direction; the current
`noiseGap` is a discrimination *proxy*, not mutual information.
-/

namespace RSA.Noise

open scoped ENNReal

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

/-- Color parameters from [degen-etal-2020]: low noise -/
def colorMatch : ℚ := 99/100
def colorMismatch : ℚ := 1/100
def colorDiscrimination : ℚ := colorMatch - colorMismatch  -- 0.98

/-- Size parameters from [degen-etal-2020]: medium noise -/
def sizeMatch : ℚ := 8/10
def sizeMismatch : ℚ := 2/10
def sizeDiscrimination : ℚ := sizeMatch - sizeMismatch  -- 0.60

/-- Material parameters (HYPOTHETICAL, not from any paper): high noise.
    [kursat-degen-2021] establishes the *ordering* (material harder
    than color) but not specific channel parameters. -/
def materialMatch : ℚ := 7/10
def materialMismatch : ℚ := 3/10
def materialDiscrimination : ℚ := materialMatch - materialMismatch  -- 0.40

/-- Orientation parameters: high discrimination (like colour).
    [giles-etal-2026] Exp 2 confirms ≥99% labelling accuracy for
    orientation (vertical vs horizontal), comparable to colour. Orientation
    is a privileged visual feature ([wolfe-horowitz-2017]) capable of
    producing pop-out effects and guiding pre-attentive search.

    Despite equal discrimination, colour is overinformed more than
    orientation — this dissociation is the key finding of Exp 2. -/
def orientationMatch : ℚ := 99/100
def orientationMismatch : ℚ := 1/100
def orientationDiscrimination : ℚ := orientationMatch - orientationMismatch  -- 0.98

/-- `ℝ≥0∞` siblings of the color/size channel parameters, grounded in the `ℚ`
    values above (`*_e_eq` below). These feed `PMF`-based RSA models built on the
    mathlib probability API (`RSA.L0OfMeaning` / `RSA.S1Belief`), where the
    literal-listener meaning is `ℝ≥0∞`-valued. -/
def colorMatch_e : ℝ≥0∞ := ENNReal.ofReal (colorMatch : ℝ)
def colorMismatch_e : ℝ≥0∞ := ENNReal.ofReal (colorMismatch : ℝ)
def sizeMatch_e : ℝ≥0∞ := ENNReal.ofReal (sizeMatch : ℝ)
def sizeMismatch_e : ℝ≥0∞ := ENNReal.ofReal (sizeMismatch : ℝ)

-- Discrimination Ordering

/-- Color has higher discrimination than size -/
theorem color_gt_size : colorDiscrimination > sizeDiscrimination := by
  norm_num [colorDiscrimination, colorMatch, colorMismatch, sizeDiscrimination, sizeMatch, sizeMismatch, materialDiscrimination, materialMatch, materialMismatch, orientationDiscrimination, orientationMatch, orientationMismatch]

/-- Size has higher discrimination than material -/
theorem size_gt_material : sizeDiscrimination > materialDiscrimination := by
  norm_num [colorDiscrimination, colorMatch, colorMismatch, sizeDiscrimination, sizeMatch, sizeMismatch, materialDiscrimination, materialMatch, materialMismatch, orientationDiscrimination, orientationMatch, orientationMismatch]

/-- Colour and orientation have equal discrimination. -/
theorem color_eq_orientation :
    colorDiscrimination = orientationDiscrimination := by
  norm_num [colorDiscrimination, colorMatch, colorMismatch, sizeDiscrimination, sizeMatch, sizeMismatch, materialDiscrimination, materialMatch, materialMismatch, orientationDiscrimination, orientationMatch, orientationMismatch]

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
  norm_num [colorDiscrimination, colorMatch, colorMismatch, sizeDiscrimination, sizeMatch, sizeMismatch, materialDiscrimination, materialMatch, materialMismatch, orientationDiscrimination, orientationMatch, orientationMismatch, difficultyToDiscrimination]

-- ════════════════════════════════════════════════════
-- Colour Privilege: Limits of Noise-Based Prediction
-- ════════════════════════════════════════════════════

/-- The noise model predicts that attributes with equal discrimination
    should be overinformed at equal rates. Colour and orientation have
    equal noise discrimination (0.98), so the noise model predicts no
    preference between them.

    [giles-etal-2026] Exp 2 falsifies this prediction: colour is
    overinformed significantly more than orientation (β = −0.97,
    95% CI = [−1.20, −0.75]) even when controlling for:
    - Perceptual discriminability (both ≥99% labelling accuracy)
    - Contextual distinctiveness (both equally salient)
    - Production effort (button-click equalises effort)
    - Word frequency (low-frequency colour terms tested)

    This means the noise model is *necessary but not sufficient*:
    discriminability drives overinformativeness (Exp 1), but something
    additional about colour — plausibly the perceptual optimality of
    colour category boundaries ([regier-etal-2007]) — produces a
    residual privilege. -/
theorem noise_model_predicts_no_colour_orientation_difference :
    colorDiscrimination = orientationDiscrimination := by
  norm_num [colorDiscrimination, colorMatch, colorMismatch, sizeDiscrimination, sizeMatch, sizeMismatch, materialDiscrimination, materialMatch, materialMismatch, orientationDiscrimination, orientationMatch, orientationMismatch]

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
def Features.PropertyDomain.noiseDiscrimination : Features.PropertyDomain → Option ℚ
  | .color       => some RSA.Noise.colorDiscrimination       -- 0.98
  | .orientation => some RSA.Noise.orientationDiscrimination  -- 0.98
  | .size        => some RSA.Noise.sizeDiscrimination         -- 0.60
  | .material    => some RSA.Noise.materialDiscrimination     -- 0.40
  | _            => none
