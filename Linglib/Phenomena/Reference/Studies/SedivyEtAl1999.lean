import Linglib.Core.PropertyDomain
import Linglib.Theories.Pragmatics.RSA.Core.Noise

/-!
# @cite{sedivy-etal-1999}

Achieving Incremental Semantic Interpretation through Contextual
Representation. *Cognition* 71(2), 109–147.

## Core Argument

Visual-world eye-tracking shows that listeners draw **contrastive
inferences** from scalar adjectives during incremental sentence
processing. When a speaker says "Pick up the tall glass" in a context
containing both a tall and a short glass, listeners fixate the target
faster and look at the contrast-set member more than in contexts
without a same-category competitor.

Three experiments (all using scalar/size adjectives: tall, short, big,
small, fat, thin, long, wide) converge on this finding. The theoretical
claim is that scalar adjectives trigger contrastive inferences because
they are *semantically restrictive* — their interpretation depends on a
contextually-determined comparison class, making their use pragmatically
marked (informative) when a contrast set is available.

The General Discussion predicts that color adjectives, being
non-restrictive (no comparison-class dependence), should NOT trigger
contrastive inferences. This prediction was later tested and confirmed
in Sedivy (2003, 2004), but challenged by @cite{ronderos-etal-2024}
who found that color adjectives DO elicit contrastive inferences
cross-linguistically.

## Connection to PropertyDomain

The scalar adjectives tested all belong to `PropertyDomain.size`, which
has `requiresComparisonClass = true`. The theoretical mechanism —
comparison-class dependence drives contrastive inference — is thus
encoded in the `PropertyDomain` infrastructure.

## Verified Data

All F-statistics, degrees of freedom, and mean values verified against
paper Tables 2–3 (Exp 1), Tables 5–7 (Exp 2), Tables 10–11 (Exp 3).
-/

namespace SedivyEtAl1999

-- ============================================================================
-- § Adjective Types
-- ============================================================================

/-- All three experiments used the same 8 scalar adjectives, all spatial
    dimension terms mapping to `PropertyDomain.size`. -/
def scalarAdjectives : List String :=
  ["tall", "short", "big", "small", "fat", "thin", "long", "wide"]

/-- All tested adjectives belong to the size domain. -/
def adjDomain : Core.PropertyDomain := .size

-- ============================================================================
-- § Experimental Design (shared)
-- ============================================================================

/-- Token typicality: how well the target exemplifies the adjective. -/
inductive TokenType where
  | good  -- target is a good exemplar (e.g., clearly tall)
  | poor  -- target is a marginal exemplar
  deriving DecidableEq, Repr

/-- Contrast condition across all experiments. -/
inductive Condition where
  | contrast    -- display includes same-category competitor differing on scalar dimension
  | noContrast  -- no same-category competitor
  deriving DecidableEq, Repr

-- ============================================================================
-- § ANOVA Results
-- ============================================================================

/-- ANOVA result with by-subjects and by-items F-statistics. -/
structure AnovaResult where
  /-- F-statistic (by subjects) -/
  F1 : Float
  /-- Denominator df (by subjects); numerator is always 1 -/
  df1 : Nat
  /-- F-statistic (by items) -/
  F2 : Float
  /-- Denominator df (by items) -/
  df2 : Nat
  /-- Significant by subjects (p < 0.05) -/
  significant : Bool
  deriving Repr

-- ============================================================================
-- § Experiment 1: Post-Nominal Scalar Adjectives (§3, N = 24)
-- ============================================================================

/-- Mean latency (ms) of first eye movement to target from adjective onset.
    Table 2: faster target fixation with contrast. -/
structure Exp1Latency where
  goodContrast : Nat      -- 479ms
  goodNoContrast : Nat    -- 571ms
  poorContrast : Nat      -- 540ms
  poorNoContrast : Nat    -- 714ms
  deriving Repr

def exp1_latency : Exp1Latency :=
  { goodContrast := 479, goodNoContrast := 571
  , poorContrast := 540, poorNoContrast := 714 }

/-- Exp 1: Main effect of contrast on target latency.
    F₁(1,23) = 8.29, P < 0.01; F₂(1,14) = 5.41, P < 0.05. -/
def exp1_latency_contrast : AnovaResult :=
  { F1 := 8.29, df1 := 23, F2 := 5.41, df2 := 14, significant := true }

/-- Proportion of trials with fixation to competitor within first two
    eye movements from adjective onset. Table 3. -/
structure Exp1CompetitorRate where
  goodContrast : Float      -- 0.67
  goodNoContrast : Float    -- 0.50
  poorContrast : Float      -- 0.68
  poorNoContrast : Float    -- 0.50
  deriving Repr

def exp1_competitor : Exp1CompetitorRate :=
  { goodContrast := 0.67, goodNoContrast := 0.50
  , poorContrast := 0.68, poorNoContrast := 0.50 }

/-- Exp 1: Main effect of contrast on competitor fixation.
    F₁(1,23) = 5.26, P < 0.05; F₂(1,14) = 5.06, P < 0.05. -/
def exp1_competitor_contrast : AnovaResult :=
  { F1 := 5.26, df1 := 23, F2 := 5.06, df2 := 14, significant := true }

-- ============================================================================
-- § Experiment 2: Prenominal Scalar Adjectives (§4.2, N = 24)
-- ============================================================================

/-- Exp 2: Effect of contrast on target latency — NOT significant.
    F₁(1,23) = 0.54, P = 0.47; F₂(1,14) = 0.66.
    Unlike Exp 1, prenominal position means the noun disambiguates
    before the contrastive inference can speed target identification. -/
def exp2_latency_contrast : AnovaResult :=
  { F1 := 0.54, df1 := 23, F2 := 0.66, df2 := 14, significant := false }

/-- Proportion of trials with competitor fixation. Table 6. -/
structure Exp2CompetitorRate where
  goodContrast : Float      -- 0.28
  goodNoContrast : Float    -- 0.08
  poorContrast : Float      -- 0.33
  poorNoContrast : Float    -- 0.20
  deriving Repr

def exp2_competitor : Exp2CompetitorRate :=
  { goodContrast := 0.28, goodNoContrast := 0.08
  , poorContrast := 0.33, poorNoContrast := 0.20 }

/-- Exp 2: Main effect of contrast on competitor fixation.
    F₁(1,23) = 8.19, P < 0.01; F₂(1,14) = 6.70, P < 0.05. -/
def exp2_competitor_contrast : AnovaResult :=
  { F1 := 8.19, df1 := 23, F2 := 6.70, df2 := 14, significant := true }

/-- Proportion of trials with fixation to contrast object. Table 7. -/
structure Exp2ContrastObjRate where
  goodContrast : Float      -- 0.44
  goodNoContrast : Float    -- 0.10
  poorContrast : Float      -- 0.41
  poorNoContrast : Float    -- 0.11
  deriving Repr

def exp2_contrastObj : Exp2ContrastObjRate :=
  { goodContrast := 0.44, goodNoContrast := 0.10
  , poorContrast := 0.41, poorNoContrast := 0.11 }

/-- Exp 2: Main effect of contrast on contrast-object fixation.
    F₁(1,23) = 32.83, P < 0.001; F₂(1,14) = 29.93, P < 0.001. -/
def exp2_contrastObj_contrast : AnovaResult :=
  { F1 := 32.83, df1 := 23, F2 := 29.93, df2 := 14, significant := true }

-- ============================================================================
-- § Experiment 3: Prenominal Scalar, Explicit Contrast Object (§4.3, N = 20)
-- ============================================================================

/-- Exp 3: Effect of contrast on target latency.
    F₁(1,18) = 6.76, P < 0.05; F₂(1,17) = 4.36, P = 0.05. -/
def exp3_latency_contrast : AnovaResult :=
  { F1 := 6.76, df1 := 18, F2 := 4.36, df2 := 17, significant := true }

/-- Exp 3: Main effect of contrast on competitor fixation.
    F₁(1,19) = 12.83, P < 0.01; F₂(1,15) = 11.73, P < 0.01. -/
def exp3_competitor_contrast : AnovaResult :=
  { F1 := 12.83, df1 := 19, F2 := 11.73, df2 := 15, significant := true }

/-- Exp 3: Main effect of contrast on contrast-object fixation.
    F₁(1,19) = 70.29, P < 0.001; F₂(1,15) = 35.96, P < 0.001. -/
def exp3_contrastObj_contrast : AnovaResult :=
  { F1 := 70.29, df1 := 19, F2 := 35.96, df2 := 15, significant := true }

-- ============================================================================
-- § Bridge: Scalar Adjectives Trigger Contrastive Inferences
-- ============================================================================

/-- Core finding: scalar adjectives trigger contrastive inferences across
    all three experiments. Evidence comes from two measures: increased
    competitor fixation (all 3 exps) and increased contrast-object
    fixation (Exps 2, 3). -/
theorem scalar_contrastive_inference :
    exp1_competitor_contrast.significant ∧
    exp2_competitor_contrast.significant ∧
    exp2_contrastObj_contrast.significant ∧
    exp3_competitor_contrast.significant ∧
    exp3_contrastObj_contrast.significant :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Contrast-object effects are very large: the F-statistics for
    contrast-object fixation are the strongest effects in the paper,
    indicating robust contrastive inference. -/
theorem contrastObj_large_effects :
    exp2_contrastObj_contrast.F1 > 30 ∧
    exp3_contrastObj_contrast.F1 > 70 := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § Bridge: Connection to PropertyDomain
-- ============================================================================

/-- All tested adjectives belong to the size domain, which requires
    comparison-class computation. -/
theorem scalar_requires_comparison_class :
    adjDomain = .size ∧
    Core.PropertyDomain.requiresComparisonClass .size = true :=
  ⟨rfl, rfl⟩

/-- The Sedivy mechanism: adjective types that require comparison-class
    computation (size domain) trigger contrastive inferences. Adjective
    types that do not require comparison-class computation (color, material)
    are predicted not to trigger contrastive inferences.

    The theoretical prediction is that `requiresComparisonClass = true`
    is a *necessary* condition for contrastive inference via the
    semantic-restrictiveness route. -/
theorem comparison_class_mechanism :
    Core.PropertyDomain.requiresComparisonClass .size = true ∧
    Core.PropertyDomain.requiresComparisonClass .color = false ∧
    Core.PropertyDomain.requiresComparisonClass .material = false :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § Bridge: Connection to Noise Discrimination
-- ============================================================================

/-- The size domain (tested here) has intermediate noise discrimination
    (0.60), between color (0.98) and material (0.40). Despite not having
    the highest discrimination, scalar adjectives robustly trigger
    contrastive inferences — suggesting the comparison-class mechanism
    operates independently of perceptual discrimination. -/
theorem size_has_intermediate_discrimination :
    Core.PropertyDomain.noiseDiscrimination .size = some RSA.Noise.sizeDiscrimination ∧
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination ∧
    RSA.Noise.sizeDiscrimination > RSA.Noise.materialDiscrimination := by
  refine ⟨rfl, ?_, ?_⟩ <;> native_decide

end SedivyEtAl1999
