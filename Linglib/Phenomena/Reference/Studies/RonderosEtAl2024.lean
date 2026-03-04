import Linglib.Core.PropertyDomain
import Linglib.Theories.Pragmatics.RSA.Core.Noise
import Linglib.Phenomena.Reference.Studies.SedivyEtAl1999

/-!
# @cite{ronderos-etal-2024}
@cite{sedivy-etal-1999}

Perceptual, Semantic, and Pragmatic Factors Affect the Derivation of
Contrastive Inferences. *Open Mind: Discoveries in Cognitive Science*
8, 1213–1227.

## Core Argument

Cross-linguistic eye-tracking (English, Hindi, Hungarian; N = 97) using
the @cite{sedivy-etal-1999} contrastive inference paradigm shows that
adjective type modulates whether listeners draw contrastive inferences:

- **Color** adjectives elicit contrastive inferences — contra
  Sedivy (2003, 2004), who argued color adjectives are used
  descriptively and therefore do not trigger contrastive interpretations.
- **Scalar** adjectives elicit contrastive inferences — replicating
  @cite{sedivy-etal-1999}.
- **Material** adjectives do NOT elicit contrastive inferences —
  interpreted as an effect of low visual salience of material properties.

Three factors interact:

1. **Perceptual**: color contrast is visually salient, material is not
2. **Semantic**: scalar adjectives require comparison-class computation
   (more distributed gaze in baseline), color/material do not
3. **Pragmatic**: informativity expectations drive contrastive inference
   only when perceptual access is fast enough

## Connection to Noise Theory

The contrastive inference pattern aligns with the noise discrimination
ordering from `RSA.Noise`: color (0.98) > size (0.60) > material (0.40).
High discrimination → strong contrastive signal → contrastive inference;
low discrimination → weak signal → no contrastive inference. This
extends @cite{kursat-degen-2021}'s production-side finding (redundant
modification rate) to the comprehension side (contrastive inference).

## Verified Data

All regression coefficients and cluster statistics verified against
paper text (§3.1–§3.4). SE is not reported for target-advantage or
baseline analyses and is omitted here.
-/

namespace Phenomena.Reference.Studies.RonderosEtAl2024

-- ============================================================================
-- § Adjective Types
-- ============================================================================

/-- The three adjective types tested.
    Maps to `Core.PropertyDomain`: color → `.color`, material → `.material`,
    scalar → `.size` (the scalar items are spatial dimensions). -/
inductive AdjType where
  | color     -- black, blue, brown, green, orange, red, white, yellow
  | material  -- cotton, glass, gold, leather, metal, paper, plastic, wooden, woolen
              -- (paper claims 8 but lists 9; possible typo)
  | scalar    -- large, narrow, short, small, tall, thick, thin, wide
  deriving DecidableEq, BEq, Repr

/-- Map adjective type to `PropertyDomain`. -/
def AdjType.toDomain : AdjType → Core.PropertyDomain
  | .color    => .color
  | .material => .material
  | .scalar   => .size

-- ============================================================================
-- § Languages
-- ============================================================================

/-- Three languages tested. -/
inductive Language where
  | english    -- N = 49 (60 recruited, 11 excluded)
  | hindi      -- N = 27
  | hungarian  -- N = 21
  deriving DecidableEq, BEq, Repr

def Language.n : Language → Nat
  | .english   => 49
  | .hindi     => 27
  | .hungarian => 21

/-- Total participants analyzed across all three languages
    (108 recruited, 97 after exclusions). -/
def totalN : Nat := Language.n .english + Language.n .hindi + Language.n .hungarian

theorem total_is_97 : totalN = 97 := rfl

-- ============================================================================
-- § Experimental Design
-- ============================================================================

/-- Contrast condition: whether the visual display contains a competitor
    object of the same category that differs on the adjective dimension. -/
inductive Condition where
  | contrast    -- target + same-category competitor differing on adjective
  | noContrast  -- target + no same-category competitor
  deriving DecidableEq, BEq, Repr

/-- Number of items per adjective type (8 adjectives × 3 nouns). -/
def itemsPerType : Nat := 24

/-- Total experimental trials (+ 72 filler trials). -/
def totalTrials : Nat := itemsPerType * 3

theorem trials_is_72 : totalTrials = 72 := rfl

-- ============================================================================
-- § Cluster-Based Permutation Analysis (§3.1)
-- ============================================================================

/-- Result from cluster-based permutation test on target-advantage
    difference curves (Contrast − No-Contrast). -/
structure ClusterResult where
  /-- Start of significant cluster (ms post-adjective onset) -/
  clusterStart : Nat
  /-- End of significant cluster (ms) -/
  clusterEnd : Nat
  /-- Sum of t-values across the cluster -/
  sumT : Float
  /-- Whether the cluster reached significance (p < 0.01) -/
  significant : Bool
  deriving Repr

/-- Color: significant cluster 240–600ms (§3.1). -/
def cluster_color : ClusterResult :=
  { clusterStart := 240, clusterEnd := 600
  , sumT := 39.61, significant := true }

/-- Scalar: significant cluster 260–500ms (§3.1). -/
def cluster_scalar : ClusterResult :=
  { clusterStart := 260, clusterEnd := 500
  , sumT := 33.07, significant := true }

/-- Material: no significant cluster (§3.1). -/
def cluster_material : ClusterResult :=
  { clusterStart := 0, clusterEnd := 0
  , sumT := 0.0, significant := false }

/-- Adjective Type × Condition interaction: significant cluster
    280–600ms (§3.1). -/
def cluster_interaction : ClusterResult :=
  { clusterStart := 280, clusterEnd := 600
  , sumT := 37.96, significant := true }

-- ============================================================================
-- § Target-Advantage Score Analysis (§3.2)
-- ============================================================================

/-- Mixed-effects regression result for target-advantage score
    (mean proportion of looks to target, 200–800ms window).
    Note: paper reports β, t, and p but not SE. -/
structure TargetAdvantageResult where
  /-- Fixed-effect coefficient (Contrast − No-Contrast) -/
  beta : Float
  /-- t-statistic -/
  tStat : Float
  /-- p-value (exact when reported, else threshold) -/
  pValue : Option Float := none
  /-- Whether effect is significant (p < 0.05) -/
  significant : Bool
  deriving Repr

/-- Color: β = 0.24, t = 2.41, p < 0.05 (§3.2). -/
def targetAdv_color : TargetAdvantageResult :=
  { beta := 0.24, tStat := 2.41, significant := true }

/-- Scalar: β = 0.19, t = 2.02, p < 0.05 (§3.2). -/
def targetAdv_scalar : TargetAdvantageResult :=
  { beta := 0.19, tStat := 2.02, significant := true }

/-- Material: β = 0.10, t = 1.08, p = 0.28 (§3.2). -/
def targetAdv_material : TargetAdvantageResult :=
  { beta := 0.10, tStat := 1.08, pValue := some 0.28, significant := false }

-- ============================================================================
-- § No-Contrast Baseline: Overall Looks (§3.3)
-- ============================================================================

/-- Baseline comparison of overall looks to both target and competitor
    in the No-Contrast condition (200–800ms). Tests whether adjective
    types differ in how efficiently participants fixate on the critical
    images, independent of contrastive inference. Positive β means more
    looks to both critical images for the first adjective type.
    Note: paper reports β, z, and p but not SE. -/
structure BaselineResult where
  /-- Fixed-effect coefficient -/
  beta : Float
  /-- z-statistic -/
  zStat : Float
  /-- Whether effect is significant -/
  significant : Bool
  deriving Repr

/-- Color vs Scalar in No-Contrast: β = 0.25, z = 2.80,
    p < 0.01 (§3.3). Participants fixated more on both critical
    images in color trials than in scalar trials. -/
def baseline_colorVsScalar : BaselineResult :=
  { beta := 0.25, zStat := 2.80, significant := true }

/-- Material vs Scalar in No-Contrast: β = 0.24, z = 2.40,
    p < 0.05 (§3.3). Participants fixated more on both critical
    images in material trials than in scalar trials.
    Interpretation: scalar adjectives require comparison-class
    computation, leading to more distributed gaze across all four
    display images including distractors. -/
def baseline_materialVsScalar : BaselineResult :=
  { beta := 0.24, zStat := 2.40, significant := true }

-- ============================================================================
-- § Pre-Noun Baseline (§3.4)
-- ============================================================================

/-- No significant effects in pre-noun window (trial onset to noun
    onset): no condition differences, no adjective-type differences,
    no interactions. Confirms effects in critical window are not due
    to anticipatory looking (§3.4). -/
def preNounBaselineClean : Bool := true

-- ============================================================================
-- § Bridge: Contrastive Inference Pattern
-- ============================================================================

/-- Color and scalar adjectives elicit contrastive inferences;
    material adjectives do not. Both cluster and target-advantage
    analyses converge. -/
theorem contrastive_inference_pattern :
    -- Cluster analysis
    cluster_color.significant ∧
    cluster_scalar.significant ∧
    ¬cluster_material.significant ∧
    -- Target-advantage score
    targetAdv_color.significant ∧
    targetAdv_scalar.significant ∧
    ¬targetAdv_material.significant :=
  ⟨rfl, rfl, by decide, rfl, rfl, by decide⟩

/-- The interaction between adjective type and condition is significant:
    the contrastive effect is not uniform across adjective types. -/
theorem interaction_significant :
    cluster_interaction.significant = true := rfl

/-- All target-advantage betas are positive: the Contrast condition
    always shows numerically more looks to target than No-Contrast,
    even for material (just not significantly). -/
theorem all_betas_positive :
    targetAdv_color.beta > 0 ∧
    targetAdv_scalar.beta > 0 ∧
    targetAdv_material.beta > 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Color has the largest contrastive effect, then scalar, then
    material: β_color > β_scalar > β_material. -/
theorem effect_size_ordering :
    targetAdv_color.beta > targetAdv_scalar.beta ∧
    targetAdv_scalar.beta > targetAdv_material.beta := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § Bridge: Semantic Factor — Scalar Adjectives Require More Processing
-- ============================================================================

/-- In the No-Contrast baseline, both color and material attract more
    fixations to the critical images (target + competitor) than scalar
    adjectives. Scalar adjectives require comparison-class computation,
    leading to more distributed gaze across all four display images. -/
theorem scalar_baseline_disadvantage :
    baseline_colorVsScalar.significant ∧
    baseline_materialVsScalar.significant := ⟨rfl, rfl⟩

-- ============================================================================
-- § Bridge: Connection to Noise Discrimination
-- ============================================================================

/-- The adjective types that elicit contrastive inferences (color,
    scalar) both have noise discrimination > 0.40 (material's value).
    The adjective type that does NOT elicit contrastive inferences
    (material) has the lowest discrimination. -/
theorem discrimination_predicts_contrastive :
    -- Color: high discrimination, contrastive inference
    AdjType.toDomain .color = .color ∧
    Core.PropertyDomain.noiseDiscrimination .color = some RSA.Noise.colorDiscrimination ∧
    targetAdv_color.significant ∧
    -- Material: low discrimination, no contrastive inference
    AdjType.toDomain .material = .material ∧
    Core.PropertyDomain.noiseDiscrimination .material = some RSA.Noise.materialDiscrimination ∧
    ¬targetAdv_material.significant ∧
    -- Discrimination ordering: color > material
    RSA.Noise.colorDiscrimination > RSA.Noise.materialDiscrimination :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, by native_decide⟩

/-- The full discrimination ordering (color > size > material) matches
    the contrastive effect ordering (β_color > β_scalar > β_material).
    Both orderings agree on which adjective types produce the strongest
    pragmatic effects. -/
theorem noise_ordering_matches_effect_ordering :
    -- Noise: color > size > material
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination ∧
    RSA.Noise.sizeDiscrimination > RSA.Noise.materialDiscrimination ∧
    -- Effects: color > scalar > material
    targetAdv_color.beta > targetAdv_scalar.beta ∧
    targetAdv_scalar.beta > targetAdv_material.beta := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Connection to @cite{kursat-degen-2021}: both studies find that
    material adjectives produce the weakest pragmatic effects.
    @cite{kursat-degen-2021} shows material is used redundantly *less*
    (production); this study shows material fails to elicit contrastive
    inferences (comprehension). Both are predicted by low noise
    discrimination for material properties. -/
theorem converging_evidence_with_kursat_degen :
    -- This study: material doesn't trigger contrastive inference
    ¬targetAdv_material.significant ∧
    -- Noise module: material discrimination is lowest
    RSA.Noise.materialDiscrimination < RSA.Noise.sizeDiscrimination ∧
    RSA.Noise.materialDiscrimination < RSA.Noise.colorDiscrimination := by
  refine ⟨by decide, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § Bridge: Cross-Study Comparison with @cite{sedivy-etal-1999}
-- ============================================================================

/-- Agreement with @cite{sedivy-etal-1999}: both studies find that
    scalar adjectives (size domain) trigger contrastive inferences.
    This study replicates the core Sedivy finding cross-linguistically. -/
theorem agrees_with_sedivy_on_scalar :
    -- This study: scalar triggers contrastive inference
    targetAdv_scalar.significant ∧
    -- Sedivy: scalar triggers across all 3 experiments
    SedivyEtAl1999.exp1_competitor_contrast.significant ∧
    SedivyEtAl1999.exp2_competitor_contrast.significant ∧
    SedivyEtAl1999.exp3_competitor_contrast.significant ∧
    -- Shared domain: scalar → size → requires comparison class
    AdjType.toDomain .scalar = .size ∧
    SedivyEtAl1999.adjDomain = .size ∧
    Core.PropertyDomain.requiresComparisonClass .size = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Disagreement with Sedivy (2003, 2004): this study finds that color
    adjectives DO trigger contrastive inferences (β = 0.24, p < 0.05),
    while Sedivy's later work argued color adjectives are used
    descriptively and do not trigger contrastive interpretations.

    The two-route model resolves this: @cite{sedivy-etal-1999}'s
    comparison-class mechanism predicts color should NOT trigger
    (it doesn't require comparison class), but the perceptual
    discrimination mechanism predicts it SHOULD trigger (color has
    the highest discrimination at 0.98). The disagreement suggests
    that perceptual salience can override the semantic-restrictiveness
    prediction. -/
theorem disagrees_with_sedivy_on_color :
    -- This study: color DOES trigger contrastive inference
    targetAdv_color.significant ∧
    -- Color does NOT require comparison class (Sedivy's mechanism predicts no inference)
    Core.PropertyDomain.requiresComparisonClass .color = false ∧
    -- But color HAS high discrimination (perceptual mechanism predicts inference)
    Core.PropertyDomain.noiseDiscrimination .color = some RSA.Noise.colorDiscrimination ∧
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination := by
  refine ⟨rfl, rfl, rfl, ?_⟩; native_decide

-- ============================================================================
-- § Bridge: Two Routes to Contrastive Inference
-- ============================================================================

/-- Two independent mechanisms can drive contrastive inference:

    1. **Semantic restrictiveness** (@cite{sedivy-etal-1999}): adjectives
       requiring comparison-class computation are pragmatically marked,
       triggering inference. Predicts: size YES, color NO, material NO.
       Confirmed by @cite{sedivy-etal-1999} across 3 experiments.

    2. **Perceptual discrimination** (@cite{ronderos-etal-2024}): high
       discrimination provides a strong pragmatic signal, enabling
       inference even for non-restrictive adjectives. Predicts: color YES
       (high discrimination despite no comparison class), material NO
       (low discrimination AND no comparison class).

    Together these explain the full pattern: size triggers inference via
    route 1, color triggers inference via route 2, material fails both. -/
theorem two_routes :
    -- Route 1: Semantic restrictiveness (Sedivy's mechanism)
    SedivyEtAl1999.adjDomain = .size ∧
    Core.PropertyDomain.requiresComparisonClass .size = true ∧
    SedivyEtAl1999.exp1_competitor_contrast.significant ∧
    -- Route 2: Perceptual discrimination (this study)
    -- Color triggers despite NOT requiring comparison class
    Core.PropertyDomain.requiresComparisonClass .color = false ∧
    Core.PropertyDomain.noiseDiscrimination .color = some RSA.Noise.colorDiscrimination ∧
    targetAdv_color.significant ∧
    -- Material: fails both routes
    Core.PropertyDomain.requiresComparisonClass .material = false ∧
    Core.PropertyDomain.noiseDiscrimination .material = some RSA.Noise.materialDiscrimination ∧
    ¬targetAdv_material.significant ∧
    -- Discrimination ordering: color >> material
    RSA.Noise.colorDiscrimination > RSA.Noise.materialDiscrimination := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, ?_⟩; native_decide

end Phenomena.Reference.Studies.RonderosEtAl2024
