import Linglib.Features.PropertyDomain
import Linglib.Theories.Pragmatics.RSA.Channel
import Linglib.Studies.DegenEtAl2020
import Linglib.Studies.WaldonDegen2021
import Linglib.Studies.EngelhardtEtAl2006

/-!
# @cite{kursat-degen-2021}
@cite{degen-etal-2020} @cite{waldon-degen-2021} @cite{engelhardt-etal-2006}

Perceptual difficulty differences predict asymmetry in redundant
modification with color and material adjectives. *Proceedings of the
Linguistic Society of America* 6(1): 676-688, 2021.

## Core Argument

Material adjectives are harder to perceive than color adjectives
(Exps 1, 3), and color adjectives are used redundantly more often than
material adjectives (Exp 2). This anti-correlation between perceptual
difficulty and redundant-use rate supports a noise-based RSA account
(@cite{waldon-degen-2021}) where the noise parameter reflects perceptual
difficulty of property verification.

## Experiments

- **Exp 1** (§2, N = 105: 120 recruited, 15 excluded): Perceptual difficulty
  norms. Participants verified whether an adjective applied to an object.
  Material adjectives produced higher error rates (β = 0.48) and slower
  RTs (β = 5.44).
- **Exp 2** (§3, N ≈ 95: 100 recruited, 5 excluded): Redundant modifier
  production. Speakers described objects in contexts where one property
  was sufficient. Color was used redundantly more than material (β = 2.32).
- **Exp 3** (§4, N = 376: 400 recruited, 24 excluded): Perceptual difficulty
  measured with Exp 2 displays. Material remained harder (error β = 0.96,
  RT β = 0.24).

## Verified Data

All regression coefficients verified against paper text (§2.3, §3.3,
§4.3).

## Derivational Chain

The cs-RSA model (@cite{degen-etal-2020}) explains redundant modification
via noisy perception. The derivation proceeds in four steps:

1. **Model structure**: The cs-RSA meaning function φ decomposes into
   independent per-feature noise channels (proven in DegenEtAl2020:
   `φ_product_of_experts`).

2. **Parameterization**: Each noise channel has match/mismatch parameters
   that determine its discrimination (noise gap). The cs-RSA model's
   default color params (0.99/0.01) match the `RSA.Noise` module's
   (proven below: `csrsa_params_match_noise`).

3. **Ordering prediction**: The noise gap determines how much signal a
   modifier provides. Color's gap (0.98) exceeds material's gap (0.40),
   so color modifiers provide more discriminative signal to the L0
   listener (proven: `color_gap_exceeds_material`).

4. **Empirical confirmation**: The predicted ordering (color more
   redundant than material) matches Exp 2 (β = 2.32, p < .0001), and
   the perceptual difficulty ordering that grounds the noise parameters
   is confirmed by Exps 1 and 3.

Note: the material noise parameters in `RSA.Noise` (0.70/0.30) are
hypothetical, not derived from this paper. This paper establishes the
*ordering* (color easier than material), not the specific channel
parameters. The full S1 redundancy prediction requires the incremental
model of @cite{waldon-degen-2021}.
-/

namespace KursatDegen2021

-- ============================================================================
-- § Property Types
-- ============================================================================

/-- Property types tested across experiments — re-exported from
    `Features.PropertyDomain` for local use. -/
abbrev PropertyType := Features.PropertyDomain

-- ============================================================================
-- § Regression Results
-- ============================================================================

/-- A regression result from one of the paper's mixed-effects models.
    Sign convention varies by experiment: in Exps 1/3, positive β means
    material > color (harder); in Exp 2, positive β means color > material
    (more redundant). See individual def docstrings for interpretation. -/
structure RegressionResult where
  /-- Fixed-effect coefficient -/
  beta : Float
  /-- Standard error -/
  se : Float
  /-- t-statistic (when reported) -/
  tStat : Option Float := none
  /-- All reported effects are p < .0001 -/
  significant : Bool
  deriving Repr

-- ============================================================================
-- § Experiment 1: Perceptual Difficulty Norms (§2, N = 105)
-- ============================================================================

/-- Material → higher error rates (§2.3: β = 0.48, SE = 0.12, p < .0001).
    Log odds of incorrect response. -/
def exp1_error : RegressionResult :=
  { beta := 0.48, se := 0.12, significant := true }

/-- Material → slower RTs (§2.3: β = 5.44, SE = 4.74, t = 11.49, p < .0001).
    RT difference in ms (material − color).
    NOTE: The paper's SE and t are inconsistent (5.44/4.74 ≈ 1.15 ≠ 11.49);
    likely SE = 0.474 (giving 5.44/0.474 ≈ 11.48). Values as printed. -/
def exp1_rt : RegressionResult :=
  { beta := 5.44, se := 4.74, tStat := some 11.49, significant := true }

-- ============================================================================
-- § Experiment 2: Redundant Modifier Production (§3, N ≈ 95)
-- ============================================================================

/-- Color used redundantly more than material (§3.3: β = 2.32, SE = 0.64,
    p < .0001). Log odds of including the redundant modifier. -/
def exp2_redundancy : RegressionResult :=
  { beta := 2.32, se := 0.64, significant := true }

/-- The strong version of the perceptual difficulty hypothesis —
    within-property-type difficulty predicts item-level redundancy —
    is not supported (§3.3: insufficient speakers for material items). -/
def strongVersionSupported : Bool := false

-- ============================================================================
-- § Experiment 3: Perceptual Difficulty in Context (§4, N = 376)
-- ============================================================================

/-- Material → higher error rates in context (§4.3: β = 0.96, SE = 0.09,
    p < .0001). -/
def exp3_error : RegressionResult :=
  { beta := 0.96, se := 0.09, significant := true }

/-- Material → slower RTs in context (§4.3: β = 0.24, SE = 0.018,
    t = −59.62, p < .0001). Log-transformed RT. -/
def exp3_rt : RegressionResult :=
  { beta := 0.24, se := 0.018, tStat := some (-59.62), significant := true }

-- ============================================================================
-- § Bridge: Difficulty Ordering
-- ============================================================================

/-- Material is harder to perceive than color: both error and RT effects
    are significant in Exp 1 (isolated properties) and Exp 3 (in context). -/
theorem material_harder :
    exp1_error.significant ∧ exp1_rt.significant ∧
    exp3_error.significant ∧ exp3_rt.significant :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- All difficulty effects have positive β: material produces more errors
    and slower RTs than color. -/
theorem difficulty_direction :
    exp1_error.beta > 0 ∧ exp1_rt.beta > 0 ∧
    exp3_error.beta > 0 ∧ exp3_rt.beta > 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § Bridge: Redundancy Ordering
-- ============================================================================

/-- Color is used redundantly more than material: positive β in Exp 2. -/
theorem color_more_redundant :
    exp2_redundancy.significant ∧ exp2_redundancy.beta > 0 := by
  exact ⟨rfl, by native_decide⟩

-- ============================================================================
-- § Bridge: Difficulty Predicts Redundancy
-- ============================================================================

/-- The core finding: perceptual difficulty and redundant use are
    anti-correlated across property types. Material is harder to perceive
    (positive β in Exps 1, 3) AND less redundantly used (positive β in
    Exp 2 means color > material). All effects significant. -/
theorem difficulty_predicts_redundancy :
    -- Material is harder (positive β = material > color)
    exp1_error.significant ∧ exp1_error.beta > 0 ∧
    exp3_error.significant ∧ exp3_error.beta > 0 ∧
    -- Color is more redundantly used (positive β = color > material)
    exp2_redundancy.significant ∧ exp2_redundancy.beta > 0 := by
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_⟩ <;> native_decide

-- ============================================================================
-- § Step 1: cs-RSA φ decomposes into noise channels
-- ============================================================================

/-! The cs-RSA model's meaning function φ (@cite{degen-etal-2020}) is a
product of independent per-feature noise channels (proven in
`DegenEtAl2020.φ_product_of_experts`). The φ function uses `RSA.Noise`
parameter values by construction — this is structural, not coincidental
(proven in `DegenEtAl2020.φ_grounded_in_noise`). -/

/-- The cs-RSA φ function uses RSA.Noise parameters by construction.
    Re-exported from the study file for local use. -/
theorem csrsa_params_match_noise :
    DegenEtAl2020.φ .blue .smallBlue = RSA.Noise.colorMatch ∧
    DegenEtAl2020.φ .blue .bigRed = RSA.Noise.colorMismatch ∧
    DegenEtAl2020.φ .small .smallBlue = RSA.Noise.sizeMatch ∧
    DegenEtAl2020.φ .small .bigBlue = RSA.Noise.sizeMismatch :=
  DegenEtAl2020.φ_grounded_in_noise

-- ============================================================================
-- § Step 2: Noise gap determines feature discrimination
-- ============================================================================

/-- Map property types to RSA Noise discrimination values (noise gap =
    onMatch − onMismatch). Larger gap → the feature provides a cleaner
    signal to the L0 listener via the cs-RSA φ function.
    Delegates to `PropertyDomain.noiseDiscrimination` for the three
    parameterized domains. -/
def propertyToDiscrimination : PropertyType → ℚ
  | .color => RSA.Noise.colorDiscrimination
  | .size => RSA.Noise.sizeDiscrimination
  | .material => RSA.Noise.materialDiscrimination
  | _ => 0  -- domains without established noise params

/-- The local `propertyToDiscrimination` agrees with the canonical
    `PropertyDomain.noiseDiscrimination` for all parameterized domains. -/
theorem propertyToDiscrimination_canonical :
    Features.PropertyDomain.noiseDiscrimination .color = some (propertyToDiscrimination .color) ∧
    Features.PropertyDomain.noiseDiscrimination .size = some (propertyToDiscrimination .size) ∧
    Features.PropertyDomain.noiseDiscrimination .material = some (propertyToDiscrimination .material) :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § Step 3: Ordering prediction — color gap > material gap
-- ============================================================================

/-- Color's noise gap (0.98) exceeds material's (0.40). In the cs-RSA
    product-of-experts model, this means a color modifier contributes a
    stronger discriminative signal to φ than a material modifier:
    φ_match/φ_mismatch = onMatch/onMismatch, which increases with gap. -/
theorem color_gap_exceeds_material :
    RSA.Noise.noiseGap RSA.Noise.colorMatch RSA.Noise.colorMismatch >
    RSA.Noise.noiseGap RSA.Noise.materialMatch RSA.Noise.materialMismatch := by
  native_decide

/-- Full discrimination ordering: color > size > material. Each step in
    this chain means the modifier provides less signal to the L0 listener,
    so the S1 speaker has less reason to include it redundantly. -/
theorem discrimination_ordering :
    propertyToDiscrimination .color > propertyToDiscrimination .size ∧
    propertyToDiscrimination .size > propertyToDiscrimination .material :=
  RSA.Noise.discrimination_ordering

-- ============================================================================
-- § Step 4: Empirical confirmation
-- ============================================================================

/-- The predicted ordering (color more redundant than material) matches
    the observed data: Exp 2 β = 2.32 > 0 (color used redundantly more),
    and the noise gap ordering (color > material) is grounded by the
    perceptual difficulty data (Exps 1 and 3). -/
theorem noise_predicts_redundancy :
    -- Theory: color gap > material gap
    propertyToDiscrimination .color > propertyToDiscrimination .material ∧
    -- Data: color used redundantly more (Exp 2)
    exp2_redundancy.significant ∧ exp2_redundancy.beta > 0 ∧
    -- Grounding: material harder to perceive (Exps 1, 3)
    exp1_error.significant ∧ exp1_error.beta > 0 ∧
    exp3_error.significant ∧ exp3_error.beta > 0 := by
  refine ⟨by native_decide, rfl, ?_, rfl, ?_, rfl, ?_⟩ <;> native_decide

-- ============================================================================
-- § Incremental Model Connection
-- ============================================================================

/-! The full redundancy prediction requires the incremental CI-RSA model
(@cite{waldon-degen-2021}), which processes utterances word-by-word. The
incremental model's three predictions are verified as theorems in
`WaldonDegen2021.lean` — here we re-export the key result showing that
redundant color > redundant size in English, which is the color/size
analogue of the color/material asymmetry tested in Exp 2. -/

/-- The CI-RSA incremental model predicts English speakers use redundant
    color more than redundant size (Waldon & Degen 2021, Prediction 1).
    This is the color/size version of the color/material asymmetry
    observed in Exp 2. -/
theorem incremental_model_predicts_color_asymmetry :
    WaldonDegen2021.englishSS.trajectoryProb ()
      .smallBlue [.small, .blue, .pin, .stop] >
    WaldonDegen2021.englishCS.trajectoryProb ()
      .smallBlue [.small, .blue, .pin, .stop] :=
  WaldonDegen2021.prediction1_english_asymmetry

-- ============================================================================
-- § Connection to @cite{engelhardt-etal-2006}
-- ============================================================================

/-- Both this study and @cite{engelhardt-etal-2006} show that speakers
    produce unnecessary modifiers. @cite{engelhardt-etal-2006} Exp 1
    finds a 31% overall over-description rate; this study's Exp 2
    further shows the rate varies by property type (β = 2.32: color >
    material). The noise model explains this variation: high-discrimination
    properties (color) provide more signal, so the S1 speaker has more
    reason to include them even when not strictly necessary. -/
theorem converging_production_with_engelhardt :
    -- Engelhardt: speakers over-describe 31% of the time
    EngelhardtEtAl2006.exp1_target_1ref.modified > 0 ∧
    -- This study: color used redundantly more than material (significant)
    exp2_redundancy.significant ∧ exp2_redundancy.beta > 0 ∧
    -- Theory: color discrimination > material discrimination
    propertyToDiscrimination .color > propertyToDiscrimination .material := by
  refine ⟨?_, rfl, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § Connection to @cite{dale-reiter-1995}
-- ============================================================================

/-- @cite{dale-reiter-1995}'s Incremental Algorithm uses a fixed
    `PreferredAttributes` list. This study's Exp 2 data — colour used
    redundantly more than material (β = 2.32) — suggests the preference
    ordering should track discrimination: higher-discrimination
    properties (colour) are preferred over lower ones (material).

    The noise discrimination ordering (colour > size > material) from
    `RSA.Noise` provides exactly this ranking, connecting D&R's
    preference-based REG to RSA's noise-based semantics. -/
theorem discrimination_predicts_preference :
    -- Noise ordering: colour > size > material
    propertyToDiscrimination .color > propertyToDiscrimination .size ∧
    propertyToDiscrimination .size > propertyToDiscrimination .material ∧
    -- Empirical: colour used redundantly more than material
    exp2_redundancy.significant ∧ exp2_redundancy.beta > 0 ∧
    -- D&R's No-Brevity is the weakest Q2 interpretation
    DaleReiter1995.BrevityInterpretation.noBrevity.strength = 0 := by
  refine ⟨by native_decide, by native_decide, rfl, ?_, rfl⟩; native_decide

end KursatDegen2021
