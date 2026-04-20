import Linglib.Core.SearchEfficiency
import Linglib.Core.Agent.SignalDetection
import Linglib.Core.Agent.Psychophysics
import Linglib.Theories.Pragmatics.RSA.Channel
import Linglib.Phenomena.Reference.Studies.KursatDegen2021
import Linglib.Phenomena.Reference.Studies.DegenEtAl2020
import Linglib.Phenomena.Reference.Studies.EngelhardtEtAl2006

/-!
# @cite{giles-etal-2026}

Search Efficiency Drives Reference Production Across Modalities,
But Colour Is Special. *Open Mind: Discoveries in Cognitive Science*
10, 236–260.

## Core Argument

Overinformativeness is communicatively efficient: speakers use redundant
modifiers to help listeners search for the referent. The rate of
overinformativeness tracks the **search efficiency** gained by adding
the modifier — the interaction of discriminability (ease of perceptual
search along the redundant attribute) and sufficiency (difficulty of
search using the sufficient attribute alone).

## Experiments

- **Exp 1** (N = 72, bat factory director task): Manipulates discriminability
  (high vs low via psychophysical staircases) and sufficiency (which
  attribute identifies the target) across two modalities — visual colour
  and auditory material. Results: overinformativeness tracks the
  discriminability × sufficiency interaction in both modalities, but
  colour is overinformed more than material even with equalized
  discriminability.

- **Exp 2** (N = 97, shape array director task): Compares redundant colour
  (high-frequency and low-frequency terms) vs redundant orientation,
  controlling for discriminability, salience (contextual distinctiveness),
  production effort (button-click), and word frequency. Result: colour
  is overinformed significantly more than orientation, ruling out
  salience, frequency, and effort as explanations.

## Key Findings

| # | Finding | Evidence | β | 95% CI |
|---|---------|----------|---|--------|
| 1 | Search efficiency: S-Low/R-High > S-High/R-Low | Exp 1 | −1.09 | [−1.35, −0.83] |
| 2 | Search efficiency: S-Low/R-High > Baseline | Exp 1 | −0.94 | [−1.20, −0.68] |
| 3 | Colour > material (cross-modal) | Exp 1 | −1.43 | [−1.65, −1.20] |
| 4 | Colour HF > orientation | Exp 2 | −0.97 | [−1.20, −0.75] |
| 5 | Colour LF ≈ Colour HF (frequency doesn't explain) | Exp 2 | −0.20 | [−0.44, 0.03] |

## Theoretical Implications

The noise discrimination model (`RSA.Noise`) correctly predicts
Finding 1–2 (discriminability drives overinformativeness) and
Finding 3 (colour > material from gap ordering). But it *incorrectly*
predicts that colour and orientation should be overinformed equally
(since both have discrimination ≈ 0.98). Finding 4 falsifies this:
colour has a **residual privilege** beyond discriminability.

## Verified Data

Regression coefficients verified against Tables 1 and 2 of the paper.
-/

set_option autoImplicit false

namespace GilesEtAl2026

open Core.SearchEfficiency

-- ============================================================================
-- §1. Regression Results
-- ============================================================================

/-- A regression coefficient from a Bayesian mixed-effects logistic model
    with 95% credible interval. -/
structure BayesianCoefficient where
  β : Float
  se : Float
  ci_lower : Float
  ci_upper : Float
  deriving Repr

/-- Whether the 95% CI excludes zero (evidence of a reliable effect). -/
def BayesianCoefficient.isSignificant (c : BayesianCoefficient) : Bool :=
  c.ci_lower > 0 || c.ci_upper < 0

-- ============================================================================
-- §2. Experiment 1: Search Efficiency Across Modalities (N = 72)
-- ============================================================================

-- Reference level: Colour-Redundant, S-Low/R-High.

/-- Intercept (Table 1). -/
def exp1_intercept : BayesianCoefficient :=
  { β := -2.50, se := 0.41, ci_lower := -3.34, ci_upper := -1.70 }

/-- Material-Redundant vs Colour-Redundant (Table 1).
    Negative β: colour is overinformed MORE than material even with
    equalized discriminability via psychophysical staircases. -/
def exp1_material_redundant : BayesianCoefficient :=
  { β := -1.43, se := 0.11, ci_lower := -1.65, ci_upper := -1.20 }

/-- Baseline vs S-Low/R-High (Table 1).
    Negative β: overinformativeness is LOWER at baseline (both attributes
    high-discriminability) than when the sufficient attribute is hard. -/
def exp1_baseline : BayesianCoefficient :=
  { β := -0.94, se := 0.13, ci_lower := -1.20, ci_upper := -0.68 }

/-- S-High/R-Low vs S-Low/R-High (Table 1).
    Negative β: overinformativeness is LOWER when the sufficient attribute
    is already search-efficient. -/
def exp1_sHighRLow : BayesianCoefficient :=
  { β := -1.09, se := 0.13, ci_lower := -1.35, ci_upper := -0.83 }

-- ============================================================================
-- §3. Experiment 2: Colour vs Orientation (N = 97)
-- ============================================================================

-- Reference level: High-Frequency Colour Terms Redundant.

/-- Intercept (Table 2). -/
def exp2_intercept : BayesianCoefficient :=
  { β := 0.97, se := 0.09, ci_lower := 0.80, ci_upper := 1.14 }

/-- Low-frequency colour terms (Table 2, sum contrasts).
    Small negative β relative to grand mean; CI includes zero →
    frequency does NOT explain colour's disproportionate use. -/
def exp2_lf_colour : BayesianCoefficient :=
  { β := -0.20, se := 0.12, ci_lower := -0.44, ci_upper := 0.03 }

/-- Orientation-redundant (Table 2, sum contrasts).
    Large negative β relative to grand mean; CI excludes zero →
    colour is overinformed SIGNIFICANTLY MORE than orientation. -/
def exp2_orientation : BayesianCoefficient :=
  { β := -0.97, se := 0.12, ci_lower := -1.20, ci_upper := -0.75 }

-- ============================================================================
-- §4. Verified Data
-- ============================================================================

/-- All Exp 1 effects are significant (95% CI excludes zero). -/
theorem exp1_all_significant :
    exp1_material_redundant.isSignificant ∧
    exp1_baseline.isSignificant ∧
    exp1_sHighRLow.isSignificant := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The colour vs orientation effect is significant. -/
theorem exp2_orientation_significant :
    exp2_orientation.isSignificant := by native_decide

/-- The low-frequency colour effect is NOT significant. -/
theorem exp2_lf_colour_not_significant :
    ¬exp2_lf_colour.isSignificant := by native_decide

-- ============================================================================
-- §5. Search Efficiency Predictions
-- ============================================================================

/-- The search efficiency ordering: S-Low/R-High > S-High/R-Low.
    When the sufficient attribute is hard to search and the redundant
    attribute facilitates search, speakers overinform more. -/
theorem search_efficiency_ordering :
    exp1_sHighRLow.isSignificant ∧ exp1_sHighRLow.β < 0 := by
  constructor <;> native_decide

/-- The search efficiency ordering: S-Low/R-High > Baseline.
    Speakers don't just mention all high-discriminability attributes;
    they selectively overinform to help difficult searches. -/
theorem search_efficiency_vs_baseline :
    exp1_baseline.isSignificant ∧ exp1_baseline.β < 0 := by
  constructor <;> native_decide

-- ============================================================================
-- §6. Bridge: Colour > Material (Cross-Modal Search Efficiency)
-- ============================================================================

/-- Colour is overinformed more than material (Exp 1), extending
    @cite{kursat-degen-2021}'s finding cross-modally.

    @cite{kursat-degen-2021} showed colour > material with visual stimuli.
    This study confirms the asymmetry persists when material is presented
    in the auditory modality via impact sounds, with discriminability
    equalized via psychophysical staircases. -/
theorem colour_exceeds_material :
    exp1_material_redundant.isSignificant ∧
    exp1_material_redundant.β < 0 := by
  constructor <;> native_decide

/-- Converging evidence with @cite{kursat-degen-2021}: both studies
    find colour used redundantly more than material. The present study
    adds cross-modal generalisation. -/
theorem converging_with_kursat_degen :
    -- This study: colour > material (cross-modal, equalized discriminability)
    exp1_material_redundant.isSignificant ∧
    -- Kursat & Degen 2021: colour > material (visual, perceptual difficulty)
    KursatDegen2021.exp2_redundancy.significant ∧
    KursatDegen2021.exp2_redundancy.beta > 0 := by
  refine ⟨?_, rfl, ?_⟩ <;> native_decide

-- ============================================================================
-- §7. Bridge: Noise Discrimination
-- ============================================================================

/-- The noise model's discrimination ordering (colour > size > material)
    is consistent with the search efficiency results of Exp 1:
    higher discrimination → more overinformativeness when redundant. -/
theorem noise_model_consistent_with_exp1 :
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination ∧
    RSA.Noise.sizeDiscrimination > RSA.Noise.materialDiscrimination :=
  RSA.Noise.discrimination_ordering

-- ============================================================================
-- §8. Colour Privilege: Limits of the Noise Model
-- ============================================================================

/-- The noise model predicts colour = orientation (both discrimination
    0.98), but the data shows colour >> orientation (β = −0.97). This
    is the central dissociation: search efficiency (noise discrimination)
    is *necessary but not sufficient* to explain overinformativeness
    patterns. Colour has a residual privilege.

    Possible explanations (General Discussion):
    1. Colour categories are optimised for perceptual communication
       (@cite{regier-etal-2007}), making colour inherently more
       search-efficient than orientation across naturalistic contexts.
    2. Speakers learn from experience that colour is a reliable
       referential strategy and deploy it even when its search
       efficiency advantage is controlled away. -/
theorem colour_privilege_residual :
    -- Theory: colour and orientation have equal discrimination
    RSA.Noise.colorDiscrimination = RSA.Noise.orientationDiscrimination ∧
    -- Data: colour is overinformed SIGNIFICANTLY more than orientation
    exp2_orientation.isSignificant ∧ exp2_orientation.β < 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Word frequency does not explain the colour privilege: low-frequency
    colour terms (teal, jade) produce overinformativeness rates
    indistinguishable from high-frequency terms (green, blue). -/
theorem frequency_does_not_explain :
    ¬exp2_lf_colour.isSignificant := by native_decide

-- ============================================================================
-- §9. Bridge: cs-RSA and Overinformativeness
-- ============================================================================

/-- The cs-RSA model (@cite{degen-etal-2020}) explains redundant
    modification via noisy perception. This study provides perceptual
    grounding for the noise parameters: discriminability measured via
    psychophysical staircases maps to the noise gap.

    The cs-RSA prediction — that higher noise gap produces more
    overinformativeness — is confirmed for the discriminability ×
    sufficiency interaction (Exp 1 display type effects). -/
theorem csrsa_grounding :
    -- cs-RSA: colour has higher noise gap than material
    RSA.Noise.noiseGap RSA.Noise.colorMatch RSA.Noise.colorMismatch >
    RSA.Noise.noiseGap RSA.Noise.materialMatch RSA.Noise.materialMismatch ∧
    -- Data: colour used redundantly more than material
    exp1_material_redundant.isSignificant := by
  constructor
  · native_decide
  · native_decide

-- ============================================================================
-- §11. Bridge: @cite{engelhardt-etal-2006} Over-Description Rates
-- ============================================================================

/-- Both this study and @cite{engelhardt-etal-2006} demonstrate that
    speakers routinely over-describe. The search efficiency view
    reinterprets these violations of Gricean Q2 as communicatively
    efficient: the "extra" information facilitates listener search. -/
theorem overinformativeness_is_efficient :
    -- Engelhardt: speakers over-describe 31% of the time
    EngelhardtEtAl2006.exp1_target_1ref.modified > 0.2 ∧
    -- This study: over-description tracks search efficiency
    exp1_sHighRLow.isSignificant := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- §12. Search Efficiency Display Types
-- ============================================================================

/-- The search efficiency prediction for each display type matches the
    empirical ordering from Exp 1. -/
theorem display_type_predictions :
    -- S-Low/R-High: search efficiency predicts overinformativeness
    searchEfficiencyPredicts .sLowRHigh = true ∧
    -- Baseline: intermediate (both attributes are search-efficient)
    searchEfficiencyPredicts .baseline = false ∧
    -- S-High/R-Low: no search benefit from redundancy
    searchEfficiencyPredicts .sHighRLow = false := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §13. Deep Unification: d' Predicts Overmodification
-- ============================================================================

/-- **Algebraic biconditional**: In a cs-RSA scene with one target and two
    distractors (cf. @cite{degen-etal-2020} §2), L0 prefers the overmodified
    form iff the redundant modifier's noise gap is positive.

    Scene structure: size is sufficient (only target is small), color is
    redundant (one distractor shares the target's color).

    - L0(target | sufficient) = sM / (sM + 2·sMM)
    - L0(target | sufficient+redundant) = sM·cM / (sMM·cM + sMM·cMM + sM·cM)

    Proved algebraically over free variables — a general property of the
    Product of Experts architecture, not a finite data check. -/
theorem overmodification_iff_positive_gap
    (sM sMM cM cMM : ℚ) (hsM : 0 < sM) (hsMM : 0 < sMM)
    (hcM : 0 < cM) (hcMM : 0 < cMM) :
    sM * cM / (sMM * cM + sMM * cMM + sM * cM) > sM / (sM + 2 * sMM) ↔
    cM > cMM := by
  have hD1 : (0:ℚ) < sM + 2 * sMM := by linarith
  have hD2 : (0:ℚ) < sMM * cM + sMM * cMM + sM * cM := by positivity
  rw [gt_iff_lt, gt_iff_lt, div_lt_div_iff₀ hD1 hD2]
  constructor
  · intro h
    by_contra hle; push_neg at hle
    have : sM * cM * (sM + 2 * sMM) ≤
           sM * (sMM * cM + sMM * cMM + sM * cM) := by
      nlinarith [mul_pos hsM hsMM]
    linarith
  · intro h
    nlinarith [mul_pos hsM hsMM]

/-- **d' predicts overmodification**: The SDT sensitivity d' for the
    redundant feature is positive iff the cs-RSA L0 prefers the overmodified
    form. This unifies three levels of linglib:

    - **Psychophysics** (`Core.SDTModel`): d' measures perceptual sensitivity
    - **Noise channel** (`RSA.Noise`): match/mismatch are hit/false-alarm rates
    - **Pragmatics** (cs-RSA PoE): L0 posterior determines speaker choice

    The match/mismatch noise parameters ARE the observer's hit rate and false
    alarm rate for feature verification. Positive d' means the observer can
    discriminate match from mismatch above chance — exactly when the redundant
    modifier carries useful information through the noise channel.

    @cite{giles-etal-2026} provide the perceptual grounding: discriminability
    measured via psychophysical staircases (d') maps to the noise parameters
    that drive overinformativeness in reference production. -/
theorem dprime_iff_overmodification
    (sM sMM cM cMM : ℚ) (hsM : 0 < sM) (hsMM : 0 < sMM)
    (hcM : 0 < cM) (hcMM : 0 < cMM)
    (hcM_lt1 : (cM : ℝ) < 1) (hcMM_lt1 : (cMM : ℝ) < 1) :
    0 < Core.dPrimeFromRates (↑cM) (↑cMM) ↔
    sM * cM / (sMM * cM + sMM * cMM + sM * cM) > sM / (sM + 2 * sMM) := by
  rw [overmodification_iff_positive_gap sM sMM cM cMM hsM hsMM hcM hcMM, gt_iff_lt]
  constructor
  · intro h
    exact_mod_cast (Core.dPrimeFromRates_pos_iff
      (by exact_mod_cast hcM) hcM_lt1 (by exact_mod_cast hcMM) hcMM_lt1).mp h
  · intro h
    exact (Core.dPrimeFromRates_pos_iff
      (by exact_mod_cast hcM) hcM_lt1 (by exact_mod_cast hcMM) hcMM_lt1).mpr
      (by exact_mod_cast h)

/-- Instantiation: for the standard @cite{degen-etal-2020} noise parameters
    (color match = 0.99, mismatch = 0.01), the redundant color modifier's
    d' is positive, so L0 prefers "small blue" over "small."

    This connects the concrete cs-RSA demonstration to the general
    `dprime_iff_overmodification` theorem. -/
theorem color_dprime_predicts_overmod :
    0 < Core.dPrimeFromRates
      (↑RSA.Noise.colorMatch) (↑RSA.Noise.colorMismatch) := by
  simp only [RSA.Noise.colorMatch, RSA.Noise.colorMismatch]
  exact (Core.dPrimeFromRates_pos_iff
    (by push_cast; norm_num) (by push_cast; norm_num)
    (by push_cast; norm_num) (by push_cast; norm_num)).mpr
    (by push_cast; norm_num)

-- ============================================================================
-- §14. Monotonicity: Likelihood Ratio Determines Overmod Strength
-- ============================================================================

/-- **Monotonicity in likelihood ratio**: For two redundant features with
    noise channels (cM₁, cMM₁) and (cM₂, cMM₂), the first produces a
    higher L0 posterior from overmodification iff its likelihood ratio
    cM₁/cMM₁ exceeds cM₂/cMM₂.

    The likelihood ratio — not the noise gap (cM − cMM) or d' alone —
    is the quantity that determines the *strength* of overmodification.
    Two features with equal d' but different likelihood ratios produce
    different overmodification rates. -/
theorem overmod_monotone_in_likelihood_ratio
    (sM sMM cM₁ cMM₁ cM₂ cMM₂ : ℚ)
    (hsM : 0 < sM) (hsMM : 0 < sMM)
    (hcM₁ : 0 < cM₁) (hcMM₁ : 0 < cMM₁)
    (hcM₂ : 0 < cM₂) (hcMM₂ : 0 < cMM₂) :
    sM * cM₁ / (sMM * cM₁ + sMM * cMM₁ + sM * cM₁) >
    sM * cM₂ / (sMM * cM₂ + sMM * cMM₂ + sM * cM₂) ↔
    cM₁ * cMM₂ > cM₂ * cMM₁ := by
  have hD₁ : (0:ℚ) < sMM * cM₁ + sMM * cMM₁ + sM * cM₁ := by positivity
  have hD₂ : (0:ℚ) < sMM * cM₂ + sMM * cMM₂ + sM * cM₂ := by positivity
  rw [gt_iff_lt, gt_iff_lt, div_lt_div_iff₀ hD₂ hD₁]
  constructor
  · intro h
    by_contra hle; push_neg at hle
    have : sM * cM₁ * (sMM * cM₂ + sMM * cMM₂ + sM * cM₂) ≤
           sM * cM₂ * (sMM * cM₁ + sMM * cMM₁ + sM * cM₁) := by
      nlinarith [mul_pos hsM hsMM]
    linarith
  · intro h
    nlinarith [mul_pos hsM hsMM]

/-- For the one-parameter noise family (x, 1−x) used in BDA fitting,
    the likelihood ratio ordering reduces to the parameter ordering:
    x₁ > x₂ iff x₁·(1−x₂) > x₂·(1−x₁). Combined with probit
    monotonicity, this gives: **higher d' → stronger overmodification**.

    This is the one-parameter specialization where d', noise gap, and
    likelihood ratio are all monotonically related — the only regime
    where "higher d'" unambiguously predicts "more overmodification." -/
theorem one_param_ratio_is_param_ordering
    (x₁ x₂ : ℚ) (_hx₁ : 0 < x₁) (_hx₁' : x₁ < 1)
    (_hx₂ : 0 < x₂) (_hx₂' : x₂ < 1) :
    x₁ * (1 - x₂) > x₂ * (1 - x₁) ↔ x₁ > x₂ := by
  rw [gt_iff_lt, gt_iff_lt]
  constructor <;> intro h <;> nlinarith

-- ============================================================================
-- §15. Symmetry-Breaking: Why Colour Is Special
-- ============================================================================

/-- The d'/likelihood-ratio model's monotonicity is *correct within*
    a feature (higher d' → more overmod, §14) but *incomplete across*
    features: two features with equal d' can have different overmod rates.

    @cite{giles-etal-2026} propose two accounts for the residual colour
    privilege:

    1. **Category optimality**: Colour naming systems are near-optimal
       partitions of perceptual space (@cite{regier-etal-2007},
       @cite{zaslavsky-etal-2019}). Colour categories maximise
       discriminability *across natural contexts*, making colour
       inherently more search-efficient than orientation even when
       within-trial d' is equalized.

    2. **Learned strategy**: Speakers learn from experience that colour
       is a reliable referential cue and deploy it as a default strategy
       even when its perceptual advantage is controlled away.

    Both accounts locate the symmetry-breaking *outside* the single-trial
    noise channel — in the ecological statistics of feature reliability
    across contexts. -/
theorem within_feature_monotonicity_but_not_across :
    -- The model correctly predicts ordering WITHIN features...
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination ∧
    RSA.Noise.sizeDiscrimination > RSA.Noise.materialDiscrimination ∧
    -- ...but fails to distinguish BETWEEN equal-d' features
    RSA.Noise.colorDiscrimination = RSA.Noise.orientationDiscrimination ∧
    -- Data: colour >> orientation despite equal d'
    exp2_orientation.isSignificant ∧ exp2_orientation.β < 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- §15. Bridge: PoE Architecture from Dimension Independence
-- ============================================================================

/-- The cs-RSA Product of Experts architecture — φ(u, o) = ∏ features,
    noiseChannel_f(u, o) — is the UNIQUE factoring consistent with
    @cite{luce-1959}'s dimension independence axiom, as proven by
    `Core.multidimensional_decomposition` in Psychophysics.lean.

    The argument chain:
    1. Dimension independence (@cite{luce-1959} §2.C): the ratio
       v(a[d↦s])/v(a) depends only on dimension d and the old/new values
    2. Decomposition theorem: under independence, v(a) = C · ∏ scale_d(a_d)
    3. cs-RSA instantiation: scale_color(match) = colorMatch = 0.99,
       scale_color(mismatch) = colorMismatch = 0.01, etc.
    4. @cite{giles-etal-2026} ground the scale parameters in d' measured
       via psychophysical staircases

    @cite{degen-etal-2020} already proves the factoring holds for the
    concrete φ (`φ_product_of_experts`). This bridge connects to the
    ABSTRACT infrastructure that shows the factoring is forced by
    independence — not an ad hoc modelling choice. -/
noncomputable def poeNoiseScales : Core.MultidimStimulus (Fin 2) (fun _ => Bool) where
  scale
    | 0, true  => ↑RSA.Noise.sizeMatch
    | 0, false => ↑RSA.Noise.sizeMismatch
    | 1, true  => ↑RSA.Noise.colorMatch
    | 1, false => ↑RSA.Noise.colorMismatch
  scale_pos
    | 0, true  => by norm_num [RSA.Noise.sizeMatch]
    | 0, false => by norm_num [RSA.Noise.sizeMismatch]
    | 1, true  => by norm_num [RSA.Noise.colorMatch]
    | 1, false => by norm_num [RSA.Noise.colorMismatch]

/-- Map each world to its (sizeMatch?, colorMatch?) feature vector,
    relative to the "small blue" target from @cite{degen-etal-2020}. -/
def worldStimulus : DegenEtAl2020.World → (Fin 2 → Bool)
  | .bigBlue   => ![true,  true]
  | .bigRed    => ![true,  false]
  | .smallBlue => ![false, true]

/-- The cs-RSA PoE φ function, expressed as a `multidim_luce` model.
    The score for each world is ∏ d, scale_d(stimulus(w)(d)), which
    equals sizeParam × colorParam — exactly the Product of Experts. -/
noncomputable def poeAsMultidimLuce :
    Core.RationalAction Unit DegenEtAl2020.World :=
  Core.multidim_luce poeNoiseScales worldStimulus

end GilesEtAl2026
