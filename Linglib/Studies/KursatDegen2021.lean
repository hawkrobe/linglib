import Linglib.Studies.WaldonDegen2021

/-!
# [kursat-degen-2021]
[degen-etal-2020] [waldon-degen-2021]

Perceptual difficulty differences predict asymmetry in redundant
modification with color and material adjectives. *Proceedings of the
Linguistic Society of America* 6(1): 676-688, 2021.

## Core Argument

Material adjectives are harder to perceive than color adjectives
(Exps 1, 3), and color adjectives are used redundantly more often than
material adjectives (Exp 2). This anti-correlation between perceptual
difficulty and redundant-use rate supports a noise-based RSA account
([waldon-degen-2021]) where the noise parameter reflects perceptual
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

## Noise-Model Connection

The cs-RSA model ([degen-etal-2020]) explains redundant modification via
noisy perception: features with higher perceptual discrimination contribute
more signal to the literal listener. This paper grounds the asymmetry
perceptually — material is harder to verify than color (Exps 1, 3), and
color is used redundantly more (Exp 2) — establishing the *ordering*
(color easier than material), not specific channel parameters. The full S1
redundancy prediction requires the incremental model of
[waldon-degen-2021] (re-exported below).
-/

namespace KursatDegen2021

-- ============================================================================
-- § Regression Results
-- ============================================================================

/-- A regression result from one of the paper's mixed-effects models.
    Sign convention varies by experiment: in Exps 1/3, positive β means
    material > color (harder); in Exp 2, positive β means color > material
    (more redundant). See individual def docstrings for interpretation. -/
structure RegressionResult where
  /-- Fixed-effect coefficient -/
  beta : ℚ
  /-- Standard error -/
  se : ℚ
  /-- t-statistic (when reported) -/
  tStat : Option ℚ := none
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
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [exp1_error, exp1_rt, exp3_error, exp3_rt]

-- ============================================================================
-- § Bridge: Redundancy Ordering
-- ============================================================================

/-- Color is used redundantly more than material: positive β in Exp 2. -/
theorem color_more_redundant :
    exp2_redundancy.significant ∧ exp2_redundancy.beta > 0 := by
  exact ⟨rfl, by norm_num [exp2_redundancy]⟩

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
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_⟩ <;> norm_num [exp1_error, exp3_error, exp2_redundancy]

-- ============================================================================
-- § Incremental Model Connection
-- ============================================================================

/-! The full redundancy prediction requires the incremental CI-RSA model
([waldon-degen-2021]), which processes utterances word-by-word. The
incremental model's three predictions are verified as theorems in
`WaldonDegen2021.lean` — here we re-export the key result showing that
redundant color > redundant size in English, which is the color/size
analogue of the color/material asymmetry tested in Exp 2. -/

/-- The CI-RSA incremental model predicts English speakers use redundant
    color more than redundant size (Waldon & Degen 2021, Prediction 1).
    This is the color/size version of the color/material asymmetry
    observed in Exp 2. Stated as the chain-rule trajectory comparison on
    the exact-ℚ speaker face. -/
theorem incremental_model_predicts_color_asymmetry :
    WaldonDegen2021.s1PMF WaldonDegen2021.allUttsEng WaldonDegen2021.csScene
        .smallBlue [] .small *
      WaldonDegen2021.s1PMF WaldonDegen2021.allUttsEng WaldonDegen2021.csScene
        .smallBlue [.small] .blue *
      WaldonDegen2021.s1PMF WaldonDegen2021.allUttsEng WaldonDegen2021.csScene
        .smallBlue [.small, .blue] .pin *
      WaldonDegen2021.s1PMF WaldonDegen2021.allUttsEng WaldonDegen2021.csScene
        .smallBlue [.small, .blue, .pin] .stop <
    WaldonDegen2021.s1PMF WaldonDegen2021.allUttsEng WaldonDegen2021.ssScene
        .smallBlue [] .small *
      WaldonDegen2021.s1PMF WaldonDegen2021.allUttsEng WaldonDegen2021.ssScene
        .smallBlue [.small] .blue *
      WaldonDegen2021.s1PMF WaldonDegen2021.allUttsEng WaldonDegen2021.ssScene
        .smallBlue [.small, .blue] .pin *
      WaldonDegen2021.s1PMF WaldonDegen2021.allUttsEng WaldonDegen2021.ssScene
        .smallBlue [.small, .blue, .pin] .stop :=
  WaldonDegen2021.prediction1_english_asymmetry

end KursatDegen2021
